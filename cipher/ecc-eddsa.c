/* ecc-eddsa.c  -  Elliptic Curve EdDSA signatures
 * Copyright (C) 2013, 2014 g10 Code GmbH
 *
 * This file is part of Libgcrypt.
 *
 * Libgcrypt is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as
 * published by the Free Software Foundation; either version 2.1 of
 * the License, or (at your option) any later version.
 *
 * Libgcrypt is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this program; if not, see <http://www.gnu.org/licenses/>.
 */

#include <config.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>

#include "g10lib.h"
#include "mpi.h"
#include "cipher.h"
#include "context.h"
#include "ec-context.h"
#include "ecc-common.h"



static void
reverse_buffer (unsigned char *buffer, unsigned int length)
{
  unsigned int tmp, i;

  for (i=0; i < length/2; i++)
    {
      tmp = buffer[i];
      buffer[i] = buffer[length-1-i];
      buffer[length-1-i] = tmp;
    }
}


/* Helper to scan a hex string. */
static gcry_mpi_t
scanval (const char *string)
{
  gpg_err_code_t rc;
  gcry_mpi_t val;

  rc = _gcry_mpi_scan (&val, GCRYMPI_FMT_HEX, string, 0, NULL);
  if (rc)
    log_fatal ("scanning ECC parameter failed: %s\n", gpg_strerror (rc));
  return val;
}



/* Encode MPI using the EdDSA scheme.  MINLEN specifies the required
   length of the buffer in bytes.  On success 0 is returned an a
   malloced buffer with the encoded point is stored at R_BUFFER; the
   length of this buffer is stored at R_BUFLEN.  */
static gpg_err_code_t
eddsa_encodempi (gcry_mpi_t mpi, unsigned int minlen,
                 unsigned char **r_buffer, unsigned int *r_buflen)
{
  unsigned char *rawmpi;
  unsigned int rawmpilen;

  rawmpi = _gcry_mpi_get_buffer (mpi, minlen, &rawmpilen, NULL);
  if (!rawmpi)
    return gpg_err_code_from_syserror ();

  *r_buffer = rawmpi;
  *r_buflen = rawmpilen;
  return 0;
}


/* Encode (X,Y) using the EdDSA scheme.  MINLEN is the required length
   in bytes for the result.  If WITH_PREFIX is set the returned buffer
   is prefixed with a 0x40 byte.  On success 0 is returned and a
   malloced buffer with the encoded point is stored at R_BUFFER; the
   length of this buffer is stored at R_BUFLEN.  */
static gpg_err_code_t
eddsa_encode_x_y (gcry_mpi_t x, gcry_mpi_t y, unsigned int minlen,
                  int with_prefix,
                  unsigned char **r_buffer, unsigned int *r_buflen)
{
  unsigned char *rawmpi;
  unsigned int rawmpilen;
  int off = with_prefix? 1:0;

  rawmpi = _gcry_mpi_get_buffer_extra (y, minlen, off?-1:0, &rawmpilen, NULL);
  if (minlen == 22 && rawmpilen == 24) {
	rawmpilen = 22; /* The value is fucked up in _gcry_mpi_get_buffer_extra -> do_get_buffer due to limbs having more than one byte */
  }
  if (!rawmpi)
    return gpg_err_code_from_syserror ();
  if (mpi_test_bit (x, 0) && rawmpilen)
    rawmpi[off + rawmpilen - 1] |= 0x80;  /* Set sign bit.  */
  if (off)
    rawmpi[0] = 0x40;

  *r_buffer = rawmpi;
  *r_buflen = rawmpilen + off;
  return 0;
}

/* Encode POINT using the EdDSA scheme.  X and Y are either scratch
   variables supplied by the caller or NULL.  CTX is the usual
   context.  If WITH_PREFIX is set the returned buffer is prefixed
   with a 0x40 byte.  On success 0 is returned and a malloced buffer
   with the encoded point is stored at R_BUFFER; the length of this
   buffer is stored at R_BUFLEN.  */
gpg_err_code_t
_gcry_ecc_eddsa_encodepoint (mpi_point_t point, mpi_ec_t ec,
                             gcry_mpi_t x_in, gcry_mpi_t y_in,
                             int with_prefix,
                             unsigned char **r_buffer, unsigned int *r_buflen)
{
  gpg_err_code_t rc;
  gcry_mpi_t x, y;

  x = x_in? x_in : mpi_new (0);
  y = y_in? y_in : mpi_new (0);

  if (_gcry_mpi_ec_get_affine (x, y, point, ec))
    {
      log_error ("eddsa_encodepoint: Failed to get affine coordinates\n");
      rc = GPG_ERR_INTERNAL;
    }
  else
    rc = eddsa_encode_x_y (x, y, ec->nbits/8, with_prefix, r_buffer, r_buflen);

  if (!x_in)
    mpi_free (x);
  if (!y_in)
    mpi_free (y);
  return rc;
}


/* Make sure that the opaque MPI VALUE is in compact EdDSA format.
   This function updates MPI if needed.  */
gpg_err_code_t
_gcry_ecc_eddsa_ensure_compact (gcry_mpi_t value, unsigned int nbits)
{
  gpg_err_code_t rc;
  const unsigned char *buf;
  unsigned int rawmpilen;
  gcry_mpi_t x, y;
  unsigned char *enc;
  unsigned int enclen;

  if (!mpi_is_opaque (value))
    return GPG_ERR_INV_OBJ;
  buf = mpi_get_opaque (value, &rawmpilen);
  if (!buf)
    return GPG_ERR_INV_OBJ;
  rawmpilen = (rawmpilen + 7)/8;

  if (rawmpilen > 1 && (rawmpilen%2))
    {
      if (buf[0] == 0x04)
        {
          /* Buffer is in SEC1 uncompressed format.  Extract y and
             compress.  */
          rc = _gcry_mpi_scan (&x, GCRYMPI_FMT_STD,
                               buf+1, (rawmpilen-1)/2, NULL);
          if (rc)
            return rc;
          rc = _gcry_mpi_scan (&y, GCRYMPI_FMT_STD,
                               buf+1+(rawmpilen-1)/2, (rawmpilen-1)/2, NULL);
          if (rc)
            {
              mpi_free (x);
              return rc;
            }

          rc = eddsa_encode_x_y (x, y, nbits/8, 0, &enc, &enclen);
          mpi_free (x);
          mpi_free (y);
          if (rc)
            return rc;

          mpi_set_opaque (value, enc, 8*enclen);
        }
      else if (buf[0] == 0x40)
        {
          /* Buffer is compressed but with our SEC1 alike compression
             indicator.  Remove that byte.  FIXME: We should write and
             use a function to manipulate an opaque MPI in place. */
          if (!_gcry_mpi_set_opaque_copy (value, buf + 1, (rawmpilen - 1)*8))
            return gpg_err_code_from_syserror ();
        }
    }

  return 0;
}


/* Recover X from Y and SIGN (which actually is a parity bit).  */
gpg_err_code_t
_gcry_ecc_eddsa_recover_x (gcry_mpi_t x, gcry_mpi_t y, int sign, mpi_ec_t ec)
{
  if (ec->dialect == ECC_DIALECT_ED25519) {
    gpg_err_code_t rc = 0;
    gcry_mpi_t u, v, v3, t;
    static gcry_mpi_t p58, seven;

    if (!p58)
      p58 = scanval("0FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFD");
    if (!seven)
      seven = mpi_set_ui (NULL, 7);

    u   = mpi_new (0);
    v   = mpi_new (0);
    v3  = mpi_new (0);
    t   = mpi_new (0);

    /* Compute u and v */
    /* u = y^2    */
    mpi_mulm (u, y, y, ec->p);
    /* v = b*y^2   */
    mpi_mulm (v, ec->b, u, ec->p);
    /* u = y^2-1  */
    mpi_sub_ui (u, u, 1);
    /* v = b*y^2+1 */
    mpi_add_ui (v, v, 1);

    /* Compute sqrt(u/v) */
    /* v3 = v^3 */
    mpi_powm (v3, v, mpi_const (MPI_C_THREE), ec->p);
    /* t = v3 * v3 * u * v = u * v^7 */
    mpi_powm (t, v, seven, ec->p);
    mpi_mulm (t, t, u, ec->p);
    /* t = t^((p-5)/8) = (u * v^7)^((p-5)/8)  */
    mpi_powm (t, t, p58, ec->p);
    /* x = t * u * v^3 = (u * v^3) * (u * v^7)^((p-5)/8) */
    mpi_mulm (t, t, u, ec->p);
    mpi_mulm (x, t, v3, ec->p);

    /* Adjust if needed.  */
    /* t = v * x^2  */
    mpi_mulm (t, x, x, ec->p);
    mpi_mulm (t, t, v, ec->p);
    /* -t == u ? x = x * sqrt(-1) */
    mpi_sub (t, ec->p, t);
    if (!mpi_cmp (t, u))
    {
      static gcry_mpi_t m1;  /* Fixme: this is not thread-safe.  */
      if (!m1)
        m1 = scanval ("2B8324804FC1DF0B2B4D00993DFBD7A72F431806AD2FE478C4EE1B274A0EA0B0");
      mpi_mulm (x, x, m1, ec->p);
      /* t = v * x^2  */
      mpi_mulm (t, x, x, ec->p);
      mpi_mulm (t, t, v, ec->p);
      /* -t == u ? x = x * sqrt(-1) */
      mpi_sub (t, ec->p, t);
      if (!mpi_cmp (t, u))
        rc = GPG_ERR_INV_OBJ;
    }

    /* Choose the desired square root according to parity */
    if (mpi_test_bit (x, 0) != !!sign)
      mpi_sub (x, ec->p, x);

    mpi_free (t);
    mpi_free (v3);
    mpi_free (v);
    mpi_free (u);

    return rc;
  } else if (ec->dialect == ECC_DIALECT_ED448 || ec->dialect == ECC_DIALECT_ED168) {
    gpg_err_code_t rc = 0;
    gcry_mpi_t u, v, u3, u5, v3, t, p34;
    static gcry_mpi_t p34_ed448, p34_ed168, five;

    if (!p34_ed448)
		p34_ed448 = scanval("3FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFBFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF");
	if (!p34_ed168)
		p34_ed168 = scanval("3FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFBF");
	if (!five)
	  five = mpi_set_ui(NULL, 5);

	if (ec->dialect == ECC_DIALECT_ED448)
		p34 = p34_ed448;
	else if (ec->dialect == ECC_DIALECT_ED168)
		p34 = p34_ed168;

    u   = mpi_new (0);
    v   = mpi_new (0);
    u3  = mpi_new (0);
    u5  = mpi_new (0);
    v3  = mpi_new (0);
    t   = mpi_new (0);

    /* Compute u and v */
    /* u = y^2    */
    mpi_mulm (u, y, y, ec->p);
    /* v = b*y^2   */
    mpi_mulm (v, ec->b, u, ec->p);
    /* u = y^2-1  */
    mpi_sub_ui (u, u, 1);
    /* v = b*y^2-1 */
    mpi_sub_ui (v, v, 1);

    /* Compute sqrt(u/v) */
    /* u3 = u^3 */
    mpi_powm (u3, u, mpi_const (MPI_C_THREE), ec->p);
    /* u5 = u^5 */
    mpi_powm (u5, u, five, ec->p);
    /* v3 = v^3 */
    mpi_powm (v3, v, mpi_const (MPI_C_THREE), ec->p);
    /* t = u5 * v3 = u^5 * v^3 */
    mpi_mulm (t, u5, v3, ec->p);
    /* t = t^((p-3)/4) = (u^5 * v^3)^((p-3)/4)  */
    mpi_powm (t, t, p34, ec->p);
    /* x = t * u^3 * v = (u^3 * v) * (u^5 * v^3)^((p-3)/4) */
    mpi_mulm (t, t, u3, ec->p);
    mpi_mulm (x, t, v, ec->p);

    /* Adjust if needed.  */
    /* t = v * x^2  */
    mpi_mulm (t, x, x, ec->p);
    mpi_mulm (t, t, v, ec->p);
    if (mpi_cmp (t, u))
      rc = GPG_ERR_INV_OBJ;

    /* Choose the desired square root according to parity */
    if (mpi_test_bit (x, 0) != !!sign)
      mpi_sub (x, ec->p, x);

    mpi_free (t);
    mpi_free (v3);
    mpi_free (u5);
    mpi_free (u3);
    mpi_free (v);
    mpi_free (u);

    return rc;
  } else {
    return GPG_ERR_NOT_IMPLEMENTED;
  }
}


/* Decode the EdDSA style encoded PK and set it into RESULT.  CTX is
   the usual curve context.  If R_ENCPK is not NULL, the encoded PK is
   stored at that address; this is a new copy to be released by the
   caller.  In contrast to the supplied PK, this is not an MPI and
   thus guaranteed to be properly padded.  R_ENCPKLEN receives the
   length of that encoded key.  */
gpg_err_code_t
_gcry_ecc_eddsa_decodepoint (gcry_mpi_t pk, mpi_ec_t ctx, mpi_point_t result,
                             unsigned char **r_encpk, unsigned int *r_encpklen)
{
  gpg_err_code_t rc;
  unsigned char *rawmpi;
  unsigned int rawmpilen;
  int sign;

  if (mpi_is_opaque (pk))
    {
      const unsigned char *buf;

      buf = mpi_get_opaque (pk, &rawmpilen);
      if (!buf)
        return GPG_ERR_INV_OBJ;
      rawmpilen = (rawmpilen + 7)/8;

      /* Handle compression prefixes.  The size of the buffer will be
         odd in this case.  */
      if (rawmpilen > 1 && (rawmpilen%2))
        {
          /* First check whether the public key has been given in
             standard uncompressed format (SEC1).  No need to recover
             x in this case.  */
          if (buf[0] == 0x04)
            {
              gcry_mpi_t x, y;

              rc = _gcry_mpi_scan (&x, GCRYMPI_FMT_STD,
                                   buf+1, (rawmpilen-1)/2, NULL);
              if (rc)
                return rc;
              rc = _gcry_mpi_scan (&y, GCRYMPI_FMT_STD,
                                   buf+1+(rawmpilen-1)/2, (rawmpilen-1)/2,NULL);
              if (rc)
                {
                  mpi_free (x);
                  return rc;
                }

              if (r_encpk)
                {
                  rc = eddsa_encode_x_y (x, y, ctx->nbits/8, 0,
                                         r_encpk, r_encpklen);
                  if (rc)
                    {
                      mpi_free (x);
                      mpi_free (y);
                      return rc;
                    }
                }
              mpi_snatch (result->x, x);
              mpi_snatch (result->y, y);
              mpi_set_ui (result->z, 1);
              return 0;
            }

          /* Check whether the public key has been prefixed with a 0x40
             byte to explicitly indicate compressed format using a SEC1
             alike prefix byte.  This is a Libgcrypt extension.  */
          if (buf[0] == 0x40)
            {
              rawmpilen--;
              buf++;
            }
        }

      /* EdDSA compressed point.  */
      rawmpi = xtrymalloc (rawmpilen? rawmpilen:1);
      if (!rawmpi)
        return gpg_err_code_from_syserror ();
      memcpy (rawmpi, buf, rawmpilen);
      reverse_buffer (rawmpi, rawmpilen);
    }
  else
    {
      /* Note: Without using an opaque MPI it is not reliable possible
         to find out whether the public key has been given in
         uncompressed format.  Thus we expect native EdDSA format.  */
      rawmpi = _gcry_mpi_get_buffer (pk, ctx->nbits/8, &rawmpilen, NULL);
      if (!rawmpi)
        return gpg_err_code_from_syserror ();
    }

  if (rawmpilen)
    {
      sign = !!(rawmpi[0] & 0x80);
      rawmpi[0] &= 0x7f;
    }
  else
    sign = 0;
  _gcry_mpi_set_buffer (result->y, rawmpi, rawmpilen, 0);
  if (r_encpk)
    {
      /* Revert to little endian.  */
      if (sign && rawmpilen)
        rawmpi[0] |= 0x80;
      reverse_buffer (rawmpi, rawmpilen);
      *r_encpk = rawmpi;
      if (r_encpklen)
        *r_encpklen = rawmpilen;
    }
  else
    xfree (rawmpi);

  rc = _gcry_ecc_eddsa_recover_x (result->x, result->y, sign, ctx);
  mpi_set_ui (result->z, 1);

  return rc;
}


/* Compute the A value as used by EdDSA.  The caller needs to provide
   the context EC and the actual secret D as an MPI.  The function
   returns a newly allocated 64 byte buffer at r_digest; the first 32
   bytes represent the A value.  NULL is returned on error and NULL
   stored at R_DIGEST.  */
gpg_err_code_t
_gcry_ecc_eddsa_compute_h_d (unsigned char **r_digest,
                             gcry_mpi_t d, mpi_ec_t ec)
{
  gpg_err_code_t rc;
  unsigned char *rawmpi = NULL;
  unsigned int rawmpilen;
  unsigned char *digest;
  int b;

  *r_digest = NULL;

  b = (ec->nbits+7)/8;
  if (b != 256/8 && b != 456/8 && b != 176/8)
    return GPG_ERR_INTERNAL; /* We only support 256, 456 or 176 bits. */

  /* Note that we clear DIGEST so we can use it as input to left pad
  the key with zeroes for hashing.  */
  digest = xtrycalloc_secure(2, b);
  if (!digest)
	  return gpg_err_code_from_syserror();

  rawmpi = _gcry_mpi_get_buffer(d, 0, &rawmpilen, NULL);
  if (!rawmpi) {
	  xfree(digest);
	  return gpg_err_code_from_syserror();
  }

  if (b == 256 / 8) {
	  gcry_buffer_t hvec[2];
	  memset(hvec, 0, sizeof hvec);

	  hvec[0].data = digest;
	  hvec[0].off = 0;
	  hvec[0].len = b > rawmpilen ? b - rawmpilen : 0;
	  hvec[1].data = rawmpi;
	  hvec[1].off = 0;
	  hvec[1].len = rawmpilen;
	  rc = _gcry_md_hash_buffers(GCRY_MD_SHA512, 0, digest, hvec, 2);
	  xfree(rawmpi);
	  if (rc) {
		  xfree(digest);
		  return rc;
	  }

	  /* Compute the A value.  */
	  reverse_buffer(digest, 32);  /* Only the first 256 bits of the hash.  */
	  digest[0] = (digest[0] & 0x7f) | 0x40;
	  digest[31] &= 0xf8;
  } else if (b == 456 / 8) {
	  digest = xtrycalloc_secure(2, b);
	  if (!digest)
		  return gpg_err_code_from_syserror();

	  unsigned char *hash_d = NULL;
	  hash_d = xtrymalloc_secure(2 * b);
	  if (!hash_d) {
		  rc = gpg_err_code_from_syserror();
		  return rc;
	  }

	  gcry_md_hd_t hd;
	  _gcry_md_open(&hd, GCRY_MD_SHAKE256, 0);
	  _gcry_md_write(hd, rawmpi, rawmpilen);
	  rc = _gcry_md_extract(hd, GCRY_MD_SHAKE256, hash_d, 2 * b);
	  _gcry_md_close(hd);
	  xfree(rawmpi);
	  if (rc) {
		  xfree(digest);
		  return rc;
	  }

	  /* Compute the A value.  */
	  reverse_buffer(hash_d, 57);  /* Only the first 456 bits.  */
	  hash_d[0] = 0x00;
	  hash_d[1] = hash_d[1] | 0x80;
	  hash_d[56] &= 0xfc;
	  memcpy(digest, hash_d, 114);
  } else if (b == 176 / 8) {
	  digest = xtrycalloc_secure(2, b);
	  if (!digest)
		  return gpg_err_code_from_syserror();

	  unsigned char *hash_d = NULL;
	  hash_d = xtrymalloc_secure(2 * b);
	  if (!hash_d) {
		  rc = gpg_err_code_from_syserror();
		  return rc;
	  }

	  gcry_md_hd_t hd;
	  _gcry_md_open(&hd, GCRY_MD_SHAKE256, 0);
	  _gcry_md_write(hd, rawmpi, rawmpilen);
	  rc = _gcry_md_extract(hd, GCRY_MD_SHAKE256, hash_d, 2 * b);
	  _gcry_md_close(hd);
	  xfree(rawmpi);
	  if (rc) {
		  xfree(digest);
		  return rc;
	  }

	  /* Compute the A value.  */
	  reverse_buffer(hash_d, 22);  /* Only the first 176 bits.  */
	  hash_d[0] = 0x00;
	  hash_d[1] = hash_d[1] | 0x80;
	  hash_d[21] &= 0xfc;
	  memcpy(digest, hash_d, 44);
  }

  *r_digest = digest;
  return 0;
}


/**
 * _gcry_ecc_eddsa_genkey - EdDSA version of the key generation.
 *
 * @sk:  A struct to receive the secret key.
 * @E:   Parameters of the curve.
 * @ctx: Elliptic curve computation context.
 * @flags: Flags controlling aspects of the creation.
 * @dbuf: Optional buffer already containing the D component.
 * @dlen: Size of this buffer.
 *
 * Return: An error code.
 *
 * The only @flags bit used by this function is %PUBKEY_FLAG_TRANSIENT
 * to use a faster RNG.
 */
gpg_err_code_t
_gcry_ecc_eddsa_genkey (ECC_secret_key *sk, elliptic_curve_t *E, mpi_ec_t ctx,
                        int flags, char *dbuf, size_t dlen)
{
 start:
  gpg_err_code_t rc;
  int b;
  if (E->dialect == ECC_DIALECT_ED25519) {
	  b = 256/8;
  } else if (E->dialect == ECC_DIALECT_ED448) {
	  b = 456/8;
  } else if (E->dialect == ECC_DIALECT_ED168) {
	  b = 176/8;
  } else {
	  rc = GPG_ERR_INTERNAL; /* We only support 256, 456, or 176 bits. */
	  goto leave;
  }
  gcry_mpi_t a, x, y;
  mpi_point_struct Q;
  gcry_random_level_t random_level;
  unsigned char *hash_d = NULL;

  point_init (&Q);

  a = mpi_snew (0);
  x = mpi_new (0);
  y = mpi_new (0);

  hash_d = xtrymalloc_secure(2 * b);
  if (!hash_d)
  {
	  rc = gpg_err_code_from_syserror();
	  goto leave;
  }

  /* Generate a secret. */
  if (dbuf == NULL) {
	  if ((flags & PUBKEY_FLAG_TRANSIENT_KEY))
		  random_level = GCRY_STRONG_RANDOM;
	  else
		  random_level = GCRY_VERY_STRONG_RANDOM;

	  dlen = b;
	  dbuf = _gcry_random_bytes_secure(dlen, random_level);
  }

  /* Compute the A value.  */
  if (E->dialect == ECC_DIALECT_ED25519) {
	  gcry_buffer_t hvec[1];
	  memset(hvec, 0, sizeof hvec);
	  hvec[0].data = dbuf;
	  hvec[0].len = dlen;
	  rc = _gcry_md_hash_buffers(GCRY_MD_SHA512, 0, hash_d, hvec, 1);
	  if (rc)
		  goto leave;
  } else if (E->dialect == ECC_DIALECT_ED448 || E->dialect == ECC_DIALECT_ED168) {
	  gcry_md_hd_t hd;
	  _gcry_md_open(&hd, GCRY_MD_SHAKE256, 0);
	  _gcry_md_write(hd, dbuf, dlen);
	  rc = _gcry_md_extract(hd, GCRY_MD_SHAKE256, hash_d, 2 * b);
	  _gcry_md_close(hd);
	  if (rc)
		  goto leave;
  }
  sk->d = _gcry_mpi_set_opaque (NULL, dbuf, dlen*8);
  dbuf = NULL;
  if (E->dialect == ECC_DIALECT_ED25519) {
	  reverse_buffer(hash_d, 32);  /* Only the first 256 bits.  */
	  hash_d[0] = (hash_d[0] & 0x7f) | 0x40;
	  hash_d[31] &= 0xf8;
	  _gcry_mpi_set_buffer(a, hash_d, 32, 0);
  } else if (E->dialect == ECC_DIALECT_ED448) {
	  reverse_buffer(hash_d, 57);  /* Only the first 456 bits.  */
	  hash_d[0] = 0x00;
	  hash_d[1] = hash_d[1] | 0x80;
	  hash_d[56] &= 0xfc;
	  _gcry_mpi_set_buffer(a, hash_d, 57, 0);
  } else if (E->dialect == ECC_DIALECT_ED168) {
	  reverse_buffer(hash_d, 22);  /* Only the first 176 bits.  */
	  hash_d[0] = 0x00;
	  hash_d[1] = hash_d[1] | 0x80;
	  hash_d[21] &= 0xfc;
	  _gcry_mpi_set_buffer(a, hash_d, 22, 0);
  }
  xfree (hash_d); hash_d = NULL;
  /* log_printmpi ("ecgen         a", a); */

  /* Compute Q.  */
  _gcry_mpi_ec_mul_point (&Q, a, &E->G, ctx);
  if (DBG_CIPHER)
    log_printpnt ("ecgen      pk", &Q, ctx);

  /* Copy the stuff to the key structures. */
  sk->E.model = E->model;
  sk->E.dialect = E->dialect;
  sk->E.p = mpi_copy(E->p);
  sk->E.a = mpi_copy(E->a);
  sk->E.b = mpi_copy(E->b);
  point_init(&sk->E.G);
  point_set(&sk->E.G, &E->G);
  sk->E.n = mpi_copy(E->n);
  sk->E.h = mpi_copy(E->h);
  point_init(&sk->Q);
  point_set(&sk->Q, &Q);

  if (E->dialect == ECC_DIALECT_ED448 || E->dialect == ECC_DIALECT_ED168) { // ECC_DIALECT_ED168 ??
	gcry_mpi_t Gx = mpi_new(0);
	gcry_mpi_t Gy = mpi_new(0);
	unsigned char *encpk;
	unsigned int encpklen;
	rc = _gcry_ecc_eddsa_encodepoint(&Q, ctx, Gx, Gy, 0, &encpk, &encpklen);
	if (rc)
		goto leave;

	gcry_mpi_t mpi_q = mpi_new(0);
	mpi_set_opaque(mpi_q, encpk, encpklen * 8);

	unsigned char *encpk2;
	unsigned int encpklen2;
	rc = _gcry_ecc_eddsa_decodepoint(mpi_q, ctx, &Q, &encpk2, &encpklen2);
	if (rc) {
		// Sometimes _gcry_ecc_eddsa_recover_x cannot find a solution x for the point to decode and returns GPG_ERR_INV_OBJ.
		// Not sure if that's normal, but in this case we just repeat the keygen process.
		point_free(&Q);
		_gcry_mpi_release(a);
		_gcry_mpi_release(x);
		_gcry_mpi_release(y);
		xfree(hash_d);
		goto start;
	}
  }

 leave:
  point_free(&Q);
  _gcry_mpi_release (a);
  _gcry_mpi_release (x);
  _gcry_mpi_release (y);
  xfree(hash_d);
  return rc;
}


/* Compute an EdDSA signature. See:
 *   [ed25519] 23pp. (PDF) Daniel J. Bernstein, Niels Duif, Tanja
 *   Lange, Peter Schwabe, Bo-Yin Yang. High-speed high-security
 *   signatures.  Journal of Cryptographic Engineering 2 (2012), 77-89.
 *   Document ID: a1a62a2f76d23f65d622484ddd09caf8.
 *   URL: http://cr.yp.to/papers.html#ed25519. Date: 2011.09.26.
 *
 * Despite that this function requires the specification of a hash
 * algorithm, we only support what has been specified by the paper.
 * This may change in the future.  Note that we don't check the used
 * curve; the user is responsible to use Ed25519.
 *
 * Return the signature struct (r,s) from the message hash.  The caller
 * must have allocated R_R and S.
 */
gpg_err_code_t
_gcry_ecc_eddsa_sign (gcry_mpi_t input, ECC_secret_key *skey,
                      gcry_mpi_t r_r, gcry_mpi_t s, int hashalgo, gcry_mpi_t pk)
{
  int rc;
  mpi_ec_t ctx = NULL;
  int b;
  unsigned int tmp;
  unsigned char *digest = NULL;
  gcry_buffer_t hvec[3];
  const void *mbuf;
  size_t mlen;
  unsigned char *rawmpi = NULL;
  unsigned int rawmpilen;
  unsigned char *encpk = NULL; /* Encoded public key.  */
  unsigned int encpklen;
  mpi_point_struct I;          /* Intermediate value.  */
  mpi_point_struct Q;          /* Public key.  */
  gcry_mpi_t a, x, y, r;

  memset (hvec, 0, sizeof hvec);

  if (!mpi_is_opaque (input))
    return GPG_ERR_INV_DATA;

  /* Initialize some helpers.  */
  point_init (&I);
  point_init (&Q);
  a = mpi_snew (0);
  x = mpi_new (0);
  y = mpi_new (0);
  r = mpi_snew (0);
  ctx = _gcry_mpi_ec_p_internal_new (skey->E.model, skey->E.dialect, 0,
                                     skey->E.p, skey->E.a, skey->E.b);
  b = (ctx->nbits+7)/8;
  if (skey->E.dialect == ECC_DIALECT_ED25519) {
	  if (b != 256/8) {
		  rc = GPG_ERR_INTERNAL; /* We only support 256 bit. */
		  goto leave;
	  }

	  rc = _gcry_ecc_eddsa_compute_h_d(&digest, skey->d, ctx);
	  if (rc)
		  goto leave;
	  _gcry_mpi_set_buffer(a, digest, 32, 0);

	  /* Compute the public key if it has not been supplied as optional
	  parameter.  */
	  if (pk)
	  {
		  rc = _gcry_ecc_eddsa_decodepoint(pk, ctx, &Q, &encpk, &encpklen);
		  if (rc)
			  goto leave;
		  if (DBG_CIPHER)
			  log_printhex("* e_pk", encpk, encpklen);
		  if (!_gcry_mpi_ec_curve_point(&Q, ctx))
		  {
			  rc = GPG_ERR_BROKEN_PUBKEY;
			  goto leave;
		  }
	  }
	  else
	  {
		  _gcry_mpi_ec_mul_point(&Q, a, &skey->E.G, ctx);
		  rc = _gcry_ecc_eddsa_encodepoint(&Q, ctx, x, y, 0, &encpk, &encpklen);
		  if (rc)
			  goto leave;
		  if (DBG_CIPHER)
			  log_printhex("  e_pk", encpk, encpklen);
	  }

	  /* Compute R.  */
	  mbuf = mpi_get_opaque(input, &tmp);
	  mlen = (tmp + 7) / 8;
	  if (DBG_CIPHER)
		  log_printhex("     m", mbuf, mlen);

	  hvec[0].data = digest;
	  hvec[0].off = 32;
	  hvec[0].len = 32;
	  hvec[1].data = (char*)mbuf;
	  hvec[1].len = mlen;
	  rc = _gcry_md_hash_buffers(hashalgo, 0, digest, hvec, 2);
	  if (rc)
		  goto leave;
	  reverse_buffer(digest, 64);
	  _gcry_mpi_set_buffer(r, digest, 64, 0);
	  mpi_mod(r, r, skey->E.n);
	  if (DBG_CIPHER)
	  log_mpidump("     r", r);
	  _gcry_mpi_ec_mul_point(&I, r, &skey->E.G, ctx);
	  if (DBG_CIPHER)
		  log_printpnt("   r", &I, 0);

	  /* Convert R into affine coordinates and apply encoding.  */
	  rc = _gcry_ecc_eddsa_encodepoint(&I, ctx, x, y, 0, &rawmpi, &rawmpilen);
	  if (rc)
		  goto leave;
	  if (DBG_CIPHER)
		  log_printhex("   e_r", rawmpi, rawmpilen);

	  /* S = r + a * H(encodepoint(R) + encodepoint(pk) + m) mod n  */
	  hvec[0].data = rawmpi;  /* (this is R) */
	  hvec[0].off = 0;
	  hvec[0].len = rawmpilen;
	  hvec[1].data = encpk;
	  hvec[1].off = 0;
	  hvec[1].len = encpklen;
	  hvec[2].data = (char*)mbuf;
	  hvec[2].off = 0;
	  hvec[2].len = mlen;
	  rc = _gcry_md_hash_buffers(hashalgo, 0, digest, hvec, 3);
	  if (rc)
		  goto leave;

	  /* No more need for RAWMPI thus we now transfer it to R_R.  */
	  mpi_set_opaque(r_r, rawmpi, rawmpilen * 8);
	  rawmpi = NULL;

	  reverse_buffer(digest, 64);
	  if (DBG_CIPHER)
		  log_printhex(" H(R+)", digest, 64);
	  _gcry_mpi_set_buffer(s, digest, 64, 0);
	  mpi_mulm(s, s, a, skey->E.n);
	  mpi_addm(s, s, r, skey->E.n);
	  rc = eddsa_encodempi(s, b, &rawmpi, &rawmpilen);
	  if (rc)
		  goto leave;
	  if (DBG_CIPHER)
		  log_printhex("   e_s", rawmpi, rawmpilen);
	  mpi_set_opaque(s, rawmpi, rawmpilen * 8);
	  rawmpi = NULL;
  } else if (skey->E.dialect == ECC_DIALECT_ED448) {
	  if (b != 456/8) {
		  rc = GPG_ERR_INTERNAL; /* We only support 456 bit. */
		  goto leave;
	  }

	  rc = _gcry_ecc_eddsa_compute_h_d(&digest, skey->d, ctx);
	  if (rc)
		  goto leave;
	  _gcry_mpi_set_buffer(a, digest, 57, 0);

	  /* Compute the public key if it has not been supplied as optional
	  parameter.  */
	  if (pk)
	  {
		  rc = _gcry_ecc_eddsa_decodepoint(pk, ctx, &Q, &encpk, &encpklen);
		  if (rc)
			  goto leave;
		  if (DBG_CIPHER)
			  log_printhex("* e_pk", encpk, encpklen);
		  if (!_gcry_mpi_ec_curve_point(&Q, ctx))
		  {
			  rc = GPG_ERR_BROKEN_PUBKEY;
			  goto leave;
		  }
	  }
	  else
	  {
		  _gcry_mpi_ec_mul_point(&Q, a, &skey->E.G, ctx);
		  rc = _gcry_ecc_eddsa_encodepoint(&Q, ctx, x, y, 0, &encpk, &encpklen);
		  if (rc)
			  goto leave;
		  if (DBG_CIPHER)
			  log_printhex("  e_pk", encpk, encpklen);
	  }

	  /* Compute R.  */
	  mbuf = mpi_get_opaque(input, &tmp);
	  mlen = (tmp + 7) / 8;
	  if (DBG_CIPHER)
		  log_printhex("     m", mbuf, mlen);

	  unsigned char *hash_d = NULL;
	  hash_d = xtrymalloc_secure(2 * b);
	  if (!hash_d) {
		  rc = gpg_err_code_from_syserror();
		  goto leave;
	  }

	  gcry_md_hd_t hd;
	  _gcry_md_open(&hd, GCRY_MD_SHAKE256, 0);
	  _gcry_md_write(hd, digest+57, 57);
	  _gcry_md_write(hd, mbuf, mlen);
	  rc = _gcry_md_extract(hd, GCRY_MD_SHAKE256, hash_d, 2 * b);
	  _gcry_md_close(hd);
	  if (rc)
		  goto leave;

	  reverse_buffer(hash_d, 114);
	  _gcry_mpi_set_buffer(r, hash_d, 114, 0);
	  mpi_mod(r, r, skey->E.n);
	  if (DBG_CIPHER)
	      log_mpidump("     r", r);
	  _gcry_mpi_ec_mul_point(&I, r, &skey->E.G, ctx);
	  if (DBG_CIPHER)
		  log_printpnt("   r", &I, 0);

	  /* Convert R into affine coordinates and apply encoding.  */
	  rc = _gcry_ecc_eddsa_encodepoint(&I, ctx, x, y, 0, &rawmpi, &rawmpilen);
	  if (rc)
		  goto leave;
	  if (DBG_CIPHER)
		  log_printhex("   e_r", rawmpi, rawmpilen);

	  /* S = r + a * H(encodepoint(R) + encodepoint(pk) + m) mod n  */
	  gcry_md_hd_t hd2;
	  _gcry_md_open(&hd2, GCRY_MD_SHAKE256, 0);
	  _gcry_md_write(hd2, rawmpi, rawmpilen);
	  _gcry_md_write(hd2, encpk, encpklen);
	  _gcry_md_write(hd2, mbuf, mlen);
	  rc = _gcry_md_extract(hd2, GCRY_MD_SHAKE256, hash_d, 2 * b);
	  _gcry_md_close(hd2);
	  if (rc)
		  goto leave;

	  /* No more need for RAWMPI thus we now transfer it to R_R.  */
	  mpi_set_opaque(r_r, rawmpi, rawmpilen * 8);
	  rawmpi = NULL;

	  reverse_buffer(hash_d, 114);
	  if (DBG_CIPHER)
		  log_printhex(" H(R+)", hash_d, 114);
	  _gcry_mpi_set_buffer(s, hash_d, 114, 0);
	  mpi_mulm(s, s, a, skey->E.n);
	  mpi_addm(s, s, r, skey->E.n);
	  rc = eddsa_encodempi(s, b, &rawmpi, &rawmpilen);
	  if (rc)
		  goto leave;
	  if (DBG_CIPHER)
		  log_printhex("   e_s", rawmpi, rawmpilen);
	  mpi_set_opaque(s, rawmpi, rawmpilen * 8);
	  rawmpi = NULL;
  } else if (skey->E.dialect == ECC_DIALECT_ED168) {
	 if (b != 176 / 8) {
		 rc = GPG_ERR_INTERNAL; /* We only support 176 bit. */
		 goto leave;
	 }

	 rc = _gcry_ecc_eddsa_compute_h_d(&digest, skey->d, ctx);
	 if (rc)
		 goto leave;
	 _gcry_mpi_set_buffer(a, digest, 22, 0);

	 /* Compute the public key if it has not been supplied as optional
	 parameter.  */
	 if (pk)
	 {
		 rc = _gcry_ecc_eddsa_decodepoint(pk, ctx, &Q, &encpk, &encpklen);
		 if (rc)
			 goto leave;
		 if (DBG_CIPHER)
			 log_printhex("* e_pk", encpk, encpklen);
		 if (!_gcry_mpi_ec_curve_point(&Q, ctx))
		 {
			 rc = GPG_ERR_BROKEN_PUBKEY;
			 goto leave;
		 }
	 }
	 else
	 {
		 _gcry_mpi_ec_mul_point(&Q, a, &skey->E.G, ctx);
		 rc = _gcry_ecc_eddsa_encodepoint(&Q, ctx, x, y, 0, &encpk, &encpklen);
		 if (rc)
			 goto leave;
		 if (DBG_CIPHER)
			 log_printhex("  e_pk", encpk, encpklen);
	 }

	 /* Compute R.  */
	 mbuf = mpi_get_opaque(input, &tmp);
	 mlen = (tmp + 7) / 8;
	 if (DBG_CIPHER)
		 log_printhex("     m", mbuf, mlen);

	 unsigned char *hash_d = NULL;
	 hash_d = xtrymalloc_secure(2 * b);
	 if (!hash_d) {
		 rc = gpg_err_code_from_syserror();
		 goto leave;
	 }

	 gcry_md_hd_t hd;
	 _gcry_md_open(&hd, GCRY_MD_SHAKE256, 0);
	 _gcry_md_write(hd, digest + 22, 22);
	 _gcry_md_write(hd, mbuf, mlen);
	 rc = _gcry_md_extract(hd, GCRY_MD_SHAKE256, hash_d, 2 * b);
	 _gcry_md_close(hd);
	 if (rc)
		 goto leave;

	 reverse_buffer(hash_d, 44);
	 _gcry_mpi_set_buffer(r, hash_d, 44, 0);
	 mpi_mod(r, r, skey->E.n);
	 if (DBG_CIPHER)
		 log_mpidump("     r", r);
	 _gcry_mpi_ec_mul_point(&I, r, &skey->E.G, ctx);
	 if (DBG_CIPHER)
		 log_printpnt("   r", &I, 0);

	 /* Convert R into affine coordinates and apply encoding.  */
	 rc = _gcry_ecc_eddsa_encodepoint(&I, ctx, x, y, 0, &rawmpi, &rawmpilen);
	 if (rc)
		 goto leave;
	 if (DBG_CIPHER)
		 log_printhex("   e_r", rawmpi, rawmpilen);

	 /* S = r + a * H(encodepoint(R) + encodepoint(pk) + m) mod n  */
	 gcry_md_hd_t hd2;
	 _gcry_md_open(&hd2, GCRY_MD_SHAKE256, 0);
	 _gcry_md_write(hd2, rawmpi, rawmpilen);
	 _gcry_md_write(hd2, encpk, encpklen);
	 _gcry_md_write(hd2, mbuf, mlen);
	 rc = _gcry_md_extract(hd2, GCRY_MD_SHAKE256, hash_d, 2 * b);
	 _gcry_md_close(hd2);
	 if (rc)
		 goto leave;

	 /* No more need for RAWMPI thus we now transfer it to R_R.  */
	 mpi_set_opaque(r_r, rawmpi, rawmpilen * 8);
	 rawmpi = NULL;

	 reverse_buffer(hash_d, 44);
	 if (DBG_CIPHER)
		 log_printhex(" H(R+)", hash_d, 44);
	 _gcry_mpi_set_buffer(s, hash_d, 44, 0);
	 mpi_mulm(s, s, a, skey->E.n);
	 mpi_addm(s, s, r, skey->E.n);
	 rc = eddsa_encodempi(s, b, &rawmpi, &rawmpilen);
	 if (rc)
		 goto leave;
	 if (DBG_CIPHER)
		 log_printhex("   e_s", rawmpi, rawmpilen);
	 mpi_set_opaque(s, rawmpi, rawmpilen * 8);
	 rawmpi = NULL;
 }

  rc = 0;

 leave:
  _gcry_mpi_release (a);
  _gcry_mpi_release (x);
  _gcry_mpi_release (y);
  _gcry_mpi_release (r);
  xfree (digest);
  _gcry_mpi_ec_free (ctx);
  point_free (&I);
  point_free (&Q);
  xfree (encpk);
  xfree (rawmpi);
  return rc;
}


/* Verify an EdDSA signature.  See sign_eddsa for the reference.
 * Check if R_IN and S_IN verifies INPUT.  PKEY has the curve
 * parameters and PK is the EdDSA style encoded public key.
 */
gpg_err_code_t
_gcry_ecc_eddsa_verify (gcry_mpi_t input, ECC_public_key *pkey,
                        gcry_mpi_t r_in, gcry_mpi_t s_in, int hashalgo,
                        gcry_mpi_t pk)
{
  int rc;
  mpi_ec_t ctx = NULL;
  int b;
  unsigned int tmp;
  mpi_point_struct Q;          /* Public key.  */
  unsigned char *encpk = NULL; /* Encoded public key.  */
  unsigned int encpklen;
  mpi_point_struct R;
  const void *mbuf;
  unsigned char *rbuf;
  size_t mlen, rlen;
  gcry_mpi_t h, s;
  mpi_point_struct Lhs, Rhs;
  gcry_mpi_t xn1, xn2, yn1, yn2;

  if (!mpi_is_opaque (input) || !mpi_is_opaque (r_in) || !mpi_is_opaque (s_in))
    return GPG_ERR_INV_DATA;

  point_init(&Q);
  point_init(&R);
  point_init(&Lhs);
  point_init(&Rhs);
  h = mpi_new(0);
  s = mpi_new(0);
  xn1 = mpi_new(0);
  xn2 = mpi_new(0);
  yn1 = mpi_new(0);
  yn2 = mpi_new(0);

  ctx = _gcry_mpi_ec_p_internal_new (pkey->E.model, pkey->E.dialect, 0,
                                     pkey->E.p, pkey->E.a, pkey->E.b);
  b = ctx->nbits/8;
  if (b == 256 / 8) {
	  if (hashalgo != GCRY_MD_SHA512)
		  return GPG_ERR_DIGEST_ALGO;
  } else if (b == 456 / 8) {
	  if (hashalgo != GCRY_MD_SHAKE256)
		  return GPG_ERR_DIGEST_ALGO;
  } else if (b == 176 / 8) {
	  if (hashalgo != GCRY_MD_SHAKE256)
		  return GPG_ERR_DIGEST_ALGO;
  } else {
	  return GPG_ERR_INTERNAL; /* We only support 256, 456, or 176 bits. */
  }

  /* Decode and check the public key.  */
  rc = _gcry_ecc_eddsa_decodepoint (pk, ctx, &Q, &encpk, &encpklen);
  if (rc)
    goto leave;
  if (!_gcry_mpi_ec_curve_point (&Q, ctx))
    {
      rc = GPG_ERR_BROKEN_PUBKEY;
      goto leave;
    }
  if (DBG_CIPHER)
    log_printhex ("  e_pk", encpk, encpklen);
  if (encpklen != b)
    {
      rc = GPG_ERR_INV_LENGTH;
      goto leave;
    }


  /* Convert the other input parameters.  */
  mbuf = mpi_get_opaque (input, &tmp);
  mlen = (tmp +7)/8;
  if (DBG_CIPHER)
    log_printhex ("     m", mbuf, mlen);
  rbuf = mpi_get_opaque (r_in, &tmp);
  rlen = (tmp +7)/8;
  if (DBG_CIPHER)
    log_printhex ("     r", rbuf, rlen);
  if (rlen != b)
    {
      rc = GPG_ERR_INV_LENGTH;
      goto leave;
    }

  /* h = H(encodepoint(R) + encodepoint(pk) + m)  */
  if (b == 256 / 8) {
	  unsigned char digest[64];
	  gcry_buffer_t hvec[3];
	  hvec[0].data = (char*)rbuf;
	  hvec[0].off  = 0;
	  hvec[0].len  = rlen;
	  hvec[1].data = encpk;
	  hvec[1].off  = 0;
	  hvec[1].len  = encpklen;
	  hvec[2].data = (char*)mbuf;
	  hvec[2].off  = 0;
	  hvec[2].len  = mlen;
	  rc = _gcry_md_hash_buffers (hashalgo, 0, digest, hvec, 3);
	  if (rc)
		goto leave;
	  reverse_buffer (digest, 64);
	  if (DBG_CIPHER)
		log_printhex (" H(R+)", digest, 64);
	  _gcry_mpi_set_buffer (h, digest, 64, 0);
  } else if (b == 456 / 8) {
	  unsigned char *hash_d = NULL;
	  hash_d = xtrymalloc_secure(2 * b);
	  if (!hash_d) {
		  rc = gpg_err_code_from_syserror();
		  goto leave;
	  }

	  gcry_md_hd_t hd;
	  _gcry_md_open(&hd, GCRY_MD_SHAKE256, 0);
	  _gcry_md_write(hd, rbuf, rlen);
	  _gcry_md_write(hd, encpk, encpklen);
	  _gcry_md_write(hd, mbuf, mlen);
	  rc = _gcry_md_extract(hd, GCRY_MD_SHAKE256, hash_d, 2 * b);
	  _gcry_md_close(hd);
	  if (rc)
		  goto leave;
	  reverse_buffer(hash_d, 114);
	  if (DBG_CIPHER)
		  log_printhex(" H(R+)", hash_d, 114);
	  _gcry_mpi_set_buffer(h, hash_d, 114, 0);
  } else if (b == 176 / 8) {
	  unsigned char *hash_d = NULL;
	  hash_d = xtrymalloc_secure(2 * b);
	  if (!hash_d) {
		  rc = gpg_err_code_from_syserror();
		  goto leave;
	  }

	  gcry_md_hd_t hd;
	  _gcry_md_open(&hd, GCRY_MD_SHAKE256, 0);
	  _gcry_md_write(hd, rbuf, rlen);
	  _gcry_md_write(hd, encpk, encpklen);
	  _gcry_md_write(hd, mbuf, mlen);
	  rc = _gcry_md_extract(hd, GCRY_MD_SHAKE256, hash_d, 2 * b);
	  _gcry_md_close(hd);
	  if (rc)
		  goto leave;
	  reverse_buffer(hash_d, 44);
	  if (DBG_CIPHER)
		  log_printhex(" H(R+)", hash_d, 44);
	  _gcry_mpi_set_buffer(h, hash_d, 44, 0);
  }

  /* According to the paper the best way for verification is:
         encodepoint(sG - h·Q) = encodepoint(r)
     because we don't need to decode R. */
  {
    void *sbuf;
    unsigned int slen;

    sbuf = _gcry_mpi_get_opaque_copy (s_in, &tmp);
    slen = (tmp +7)/8;
    reverse_buffer (sbuf, slen);
    if (DBG_CIPHER)
      log_printhex ("     s", sbuf, slen);
    _gcry_mpi_set_buffer (s, sbuf, slen, 0);
    xfree (sbuf);
    if (slen != b)
      {
        rc = GPG_ERR_INV_LENGTH;
        goto leave;
      }
  }

  /* Decode the R part of the signature.  */
  reverse_buffer(rbuf, rlen);
  int rsign = !!(rbuf[0] & 0x80);
  rbuf[0] &= 0x7f;
  _gcry_mpi_set_ui(R.z, 1);
  _gcry_mpi_set_buffer(R.y, rbuf, rlen, 0);
  rc = _gcry_ecc_eddsa_recover_x(R.x, R.y, rsign, ctx);
  if (rc)
	  goto leave;

  _gcry_mpi_mod(h, h, pkey->E.n);
  _gcry_mpi_ec_mul_point (&Lhs, s, &pkey->E.G, ctx);
  _gcry_mpi_ec_mul_point(&Rhs, h, &Q, ctx);
  _gcry_mpi_ec_add_points(&Rhs, &R, &Rhs, ctx);
  _gcry_mpi_ec_dup_point(&Lhs, &Lhs, ctx);
  _gcry_mpi_ec_dup_point(&Rhs, &Rhs, ctx);
  _gcry_mpi_ec_dup_point(&Lhs, &Lhs, ctx);
  _gcry_mpi_ec_dup_point(&Rhs, &Rhs, ctx);

  _gcry_mpi_mul(xn1, Lhs.x, Rhs.z);
  _gcry_mpi_mod(xn1, xn1, ctx->p);
  _gcry_mpi_mul(xn2, Rhs.x, Lhs.z);
  _gcry_mpi_mod(xn2, xn2, ctx->p);
  _gcry_mpi_mul(yn1, Lhs.y, Rhs.z);
  _gcry_mpi_mod(yn1, yn1, ctx->p);
  _gcry_mpi_mul(yn2, Rhs.y, Lhs.z);
  _gcry_mpi_mod(yn2, yn2, ctx->p);

  if (_gcry_mpi_cmp(xn1, xn2) || _gcry_mpi_cmp(yn1, yn2))
    {
      rc = GPG_ERR_BAD_SIGNATURE;
      goto leave;
    }

  rc = 0;

 leave:
  _gcry_mpi_release(yn2);
  _gcry_mpi_release(yn1);
  _gcry_mpi_release(xn2);
  _gcry_mpi_release(xn1);
  xfree (encpk);
  _gcry_mpi_ec_free (ctx);
  _gcry_mpi_release (s);
  _gcry_mpi_release (h);
  point_free (&Rhs);
  point_free (&Lhs);
  point_free (&R);
  point_free (&Q);
  return rc;
}
