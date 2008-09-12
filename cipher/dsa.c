/* dsa.c - DSA signature scheme
 * Copyright (C) 1998, 2000, 2001, 2002, 2003,
 *               2006, 2008  Free Software Foundation, Inc.
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
 * License along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA
 */

#include <config.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "g10lib.h"
#include "mpi.h"
#include "cipher.h"

typedef struct
{
  gcry_mpi_t p;	    /* prime */
  gcry_mpi_t q;	    /* group order */
  gcry_mpi_t g;	    /* group generator */
  gcry_mpi_t y;	    /* g^x mod p */
} DSA_public_key;


typedef struct
{
  gcry_mpi_t p;	    /* prime */
  gcry_mpi_t q;	    /* group order */
  gcry_mpi_t g;	    /* group generator */
  gcry_mpi_t y;	    /* g^x mod p */
  gcry_mpi_t x;	    /* secret exponent */
} DSA_secret_key;


/* A sample 1024 bit DSA key used for the selftests.  */
static const char sample_secret_key[] =
"(private-key"
" (dsa"
"  (p #00AD7C0025BA1A15F775F3F2D673718391D00456978D347B33D7B49E7F32EDAB"
"      96273899DD8B2BB46CD6ECA263FAF04A28903503D59062A8865D2AE8ADFB5191"
"      CF36FFB562D0E2F5809801A1F675DAE59698A9E01EFE8D7DCFCA084F4C6F5A44"
"      44D499A06FFAEA5E8EF5E01F2FD20A7B7EF3F6968AFBA1FB8D91F1559D52D8777B#)"
"  (q #00EB7B5751D25EBBB7BD59D920315FD840E19AEBF9#)"
"  (g #1574363387FDFD1DDF38F4FBE135BB20C7EE4772FB94C337AF86EA8E49666503"
"      AE04B6BE81A2F8DD095311E0217ACA698A11E6C5D33CCDAE71498ED35D13991E"
"      B02F09AB40BD8F4C5ED8C75DA779D0AE104BC34C960B002377068AB4B5A1F984"
"      3FBA91F537F1B7CAC4D8DD6D89B0D863AF7025D549F9C765D2FC07EE208F8D15#)"
"  (y #64B11EF8871BE4AB572AA810D5D3CA11A6CDBC637A8014602C72960DB135BF46"
"      A1816A724C34F87330FC9E187C5D66897A04535CC2AC9164A7150ABFA8179827"
"      6E45831AB811EEE848EBB24D9F5F2883B6E5DDC4C659DEF944DCFD80BF4D0A20"
"      42CAA7DC289F0C5A9D155F02D3D551DB741A81695B74D4C8F477F9C7838EB0FB#)"
"  (x #11D54E4ADBD3034160F2CED4B7CD292A4EBF3EC0#)))";
/* A sample 1024 bit DSA key used for the selftests (public only).  */
static const char sample_public_key[] = 
"(public-key"
" (dsa"
"  (p #00AD7C0025BA1A15F775F3F2D673718391D00456978D347B33D7B49E7F32EDAB"
"      96273899DD8B2BB46CD6ECA263FAF04A28903503D59062A8865D2AE8ADFB5191"
"      CF36FFB562D0E2F5809801A1F675DAE59698A9E01EFE8D7DCFCA084F4C6F5A44"
"      44D499A06FFAEA5E8EF5E01F2FD20A7B7EF3F6968AFBA1FB8D91F1559D52D8777B#)"
"  (q #00EB7B5751D25EBBB7BD59D920315FD840E19AEBF9#)"
"  (g #1574363387FDFD1DDF38F4FBE135BB20C7EE4772FB94C337AF86EA8E49666503"
"      AE04B6BE81A2F8DD095311E0217ACA698A11E6C5D33CCDAE71498ED35D13991E"
"      B02F09AB40BD8F4C5ED8C75DA779D0AE104BC34C960B002377068AB4B5A1F984"
"      3FBA91F537F1B7CAC4D8DD6D89B0D863AF7025D549F9C765D2FC07EE208F8D15#)"
"  (y #64B11EF8871BE4AB572AA810D5D3CA11A6CDBC637A8014602C72960DB135BF46"
"      A1816A724C34F87330FC9E187C5D66897A04535CC2AC9164A7150ABFA8179827"
"      6E45831AB811EEE848EBB24D9F5F2883B6E5DDC4C659DEF944DCFD80BF4D0A20"
"      42CAA7DC289F0C5A9D155F02D3D551DB741A81695B74D4C8F477F9C7838EB0FB#)))";




static gcry_mpi_t gen_k (gcry_mpi_t q);
static int test_keys (DSA_secret_key *sk, unsigned int qbits);
static int check_secret_key (DSA_secret_key *sk);
static gpg_err_code_t generate (DSA_secret_key *sk,
                                unsigned int nbits,
                                unsigned int qbits,
                                gcry_mpi_t **ret_factors);
static void sign (gcry_mpi_t r, gcry_mpi_t s, gcry_mpi_t input,
                  DSA_secret_key *skey);
static int verify (gcry_mpi_t r, gcry_mpi_t s, gcry_mpi_t input,
                   DSA_public_key *pkey);

static void (*progress_cb) (void *,const char *, int, int, int );
static void *progress_cb_data;


void
_gcry_register_pk_dsa_progress (void (*cb) (void *, const char *,
                                            int, int, int),
				void *cb_data)
{
  progress_cb = cb;
  progress_cb_data = cb_data;
}


static void
progress (int c)
{
  if (progress_cb)
    progress_cb (progress_cb_data, "pk_dsa", c, 0, 0);
}


/*
 * Generate a random secret exponent k less than q.
 */
static gcry_mpi_t
gen_k( gcry_mpi_t q )
{
  gcry_mpi_t k = mpi_alloc_secure( mpi_get_nlimbs(q) );
  unsigned int nbits = mpi_get_nbits(q);
  unsigned int nbytes = (nbits+7)/8;
  char *rndbuf = NULL;

  if ( DBG_CIPHER )
    log_debug("choosing a random k ");
  for (;;) 
    {
      if( DBG_CIPHER )
        progress('.');

      if ( !rndbuf || nbits < 32 ) 
        {
          gcry_free(rndbuf);
          rndbuf = gcry_random_bytes_secure( (nbits+7)/8, GCRY_STRONG_RANDOM );
	}
      else
        { /* Change only some of the higher bits.  We could improve
	     this by directly requesting more memory at the first call
	     to get_random_bytes() and use this the here maybe it is
	     easier to do this directly in random.c. */
          char *pp = gcry_random_bytes_secure( 4, GCRY_STRONG_RANDOM );
          memcpy( rndbuf,pp, 4 );
          gcry_free(pp);
	}
      _gcry_mpi_set_buffer( k, rndbuf, nbytes, 0 );
      if ( mpi_test_bit( k, nbits-1 ) )
        mpi_set_highbit( k, nbits-1 );
      else
        {
          mpi_set_highbit( k, nbits-1 );
          mpi_clear_bit( k, nbits-1 );
	}

      if( !(mpi_cmp( k, q ) < 0) ) /* check: k < q */
        {	
          if( DBG_CIPHER )
            progress('+');
          continue; /* no  */
        }
      if( !(mpi_cmp_ui( k, 0 ) > 0) )  /* check: k > 0 */
        {
          if( DBG_CIPHER )
            progress('-');
          continue; /* no */
        }
      break;	/* okay */
    }
  gcry_free(rndbuf);
  if( DBG_CIPHER )
    progress('\n');
  
  return k;
}


/* Check that a freshly generated key actually works.  Returns 0 on success. */
static int
test_keys (DSA_secret_key *sk, unsigned int qbits)
{
  int result = -1;  /* Default to failure.  */
  DSA_public_key pk;
  gcry_mpi_t data  = gcry_mpi_new (qbits);
  gcry_mpi_t sig_a = gcry_mpi_new (qbits);
  gcry_mpi_t sig_b = gcry_mpi_new (qbits);

  /* Put the relevant parameters into a public key structure.  */
  pk.p = sk->p;
  pk.q = sk->q;
  pk.g = sk->g;
  pk.y = sk->y;

  /* Create a random plaintext.  */
  gcry_mpi_randomize (data, qbits, GCRY_WEAK_RANDOM);

  /* Sign DATA using the secret key.  */
  sign (sig_a, sig_b, data, sk);

  /* Verify the signature using the public key.  */
  if ( !verify (sig_a, sig_b, data, &pk) )
    goto leave; /* Signature does not match.  */

  /* Modify the data and check that the signing fails.  */
  gcry_mpi_add_ui (data, data, 1);
  if ( verify (sig_a, sig_b, data, &pk) )
    goto leave; /* Signature matches but should not.  */

  result = 0; /* The test succeeded.  */

 leave:
  gcry_mpi_release (sig_b);
  gcry_mpi_release (sig_a);
  gcry_mpi_release (data);
  return result;
}



/*
   Generate a DSA key pair with a key of size NBITS.
   Returns: 2 structures filled with all needed values
 	    and an array with the n-1 factors of (p-1)
 */
static gpg_err_code_t
generate (DSA_secret_key *sk, unsigned int nbits, unsigned int qbits,
          gcry_mpi_t **ret_factors )
{
  gcry_mpi_t p;    /* the prime */
  gcry_mpi_t q;    /* the 160 bit prime factor */
  gcry_mpi_t g;    /* the generator */
  gcry_mpi_t y;    /* g^x mod p */
  gcry_mpi_t x;    /* the secret exponent */
  gcry_mpi_t h, e;  /* helper */
  unsigned char *rndbuf;

  if (qbits)
    ; /* Caller supplied qbits.  Use this value.  */
  else if ( nbits >= 512 && nbits <= 1024 )
    qbits = 160;
  else if ( nbits == 2048 )
    qbits = 224;
  else if ( nbits == 3072 )
    qbits = 256;
  else if ( nbits == 7680 )
    qbits = 384;
  else if ( nbits == 15360 )
    qbits = 512;
  else
    return GPG_ERR_INV_VALUE;

  if (qbits < 160 || qbits > 512 || (qbits%8) )
    return GPG_ERR_INV_VALUE;
  if (nbits < 2*qbits || nbits > 15360)
    return GPG_ERR_INV_VALUE;

  if (nbits < 1024 && fips_mode ())
    return GPG_ERR_INV_VALUE;

  p = _gcry_generate_elg_prime( 1, nbits, qbits, NULL, ret_factors );
  /* get q out of factors */
  q = mpi_copy((*ret_factors)[0]);
  if( mpi_get_nbits(q) != qbits )
    BUG();

  /* Find a generator g (h and e are helpers).
     e = (p-1)/q */
  e = mpi_alloc( mpi_get_nlimbs(p) );
  mpi_sub_ui( e, p, 1 );
  mpi_fdiv_q( e, e, q );
  g = mpi_alloc( mpi_get_nlimbs(p) );
  h = mpi_alloc_set_ui( 1 ); /* we start with 2 */
  do
    {
      mpi_add_ui( h, h, 1 );
      /* g = h^e mod p */
      gcry_mpi_powm( g, h, e, p );
    } 
  while( !mpi_cmp_ui( g, 1 ) );  /* continue until g != 1 */

  /* Select a random number which has these properties:
   *	 0 < x < q-1
   * This must be a very good random number because this
   * is the secret part. */
  if( DBG_CIPHER )
    log_debug("choosing a random x ");
  gcry_assert( qbits >= 160 );
  x = mpi_alloc_secure( mpi_get_nlimbs(q) );
  mpi_sub_ui( h, q, 1 );  /* put q-1 into h */
  rndbuf = NULL;
  do 
    {
      if( DBG_CIPHER )
        progress('.');
      if( !rndbuf )
        rndbuf = gcry_random_bytes_secure( (qbits+7)/8,
                                           GCRY_VERY_STRONG_RANDOM );
      else 
        { /* Change only some of the higher bits (= 2 bytes)*/
          char *r = gcry_random_bytes_secure (2, GCRY_VERY_STRONG_RANDOM);
          memcpy(rndbuf, r, 2 );
          gcry_free(r);
        }

      _gcry_mpi_set_buffer( x, rndbuf, (qbits+7)/8, 0 );
      mpi_clear_highbit( x, qbits+1 );
    } 
  while ( !( mpi_cmp_ui( x, 0 )>0 && mpi_cmp( x, h )<0 ) );
  gcry_free(rndbuf);
  mpi_free( e );
  mpi_free( h );

  /* y = g^x mod p */
  y = mpi_alloc( mpi_get_nlimbs(p) );
  gcry_mpi_powm( y, g, x, p );

  if( DBG_CIPHER ) 
    {
      progress('\n');
      log_mpidump("dsa  p= ", p );
      log_mpidump("dsa  q= ", q );
      log_mpidump("dsa  g= ", g );
      log_mpidump("dsa  y= ", y );
      log_mpidump("dsa  x= ", x );
    }

  /* Copy the stuff to the key structures. */
  sk->p = p;
  sk->q = q;
  sk->g = g;
  sk->y = y;
  sk->x = x;

  /* Now we can test our keys (this should never fail!). */
  if ( test_keys (sk, qbits) )
    {
      gcry_mpi_release (sk->p); sk->p = NULL;
      gcry_mpi_release (sk->q); sk->q = NULL;
      gcry_mpi_release (sk->g); sk->g = NULL;
      gcry_mpi_release (sk->y); sk->y = NULL;
      gcry_mpi_release (sk->x); sk->x = NULL;
      fips_signal_error ("self-test after key generation failed");
      return GPG_ERR_SELFTEST_FAILED;
    }
  return 0;
}



/*
   Test whether the secret key is valid.
   Returns: if this is a valid key.
 */
static int
check_secret_key( DSA_secret_key *sk )
{
  int rc;
  gcry_mpi_t y = mpi_alloc( mpi_get_nlimbs(sk->y) );

  gcry_mpi_powm( y, sk->g, sk->x, sk->p );
  rc = !mpi_cmp( y, sk->y );
  mpi_free( y );
  return rc;
}



/*
   Make a DSA signature from HASH and put it into r and s.
 */
static void
sign(gcry_mpi_t r, gcry_mpi_t s, gcry_mpi_t hash, DSA_secret_key *skey )
{
  gcry_mpi_t k;
  gcry_mpi_t kinv;
  gcry_mpi_t tmp;

  /* Select a random k with 0 < k < q */
  k = gen_k( skey->q );

  /* r = (a^k mod p) mod q */
  gcry_mpi_powm( r, skey->g, k, skey->p );
  mpi_fdiv_r( r, r, skey->q );

  /* kinv = k^(-1) mod q */
  kinv = mpi_alloc( mpi_get_nlimbs(k) );
  mpi_invm(kinv, k, skey->q );

  /* s = (kinv * ( hash + x * r)) mod q */
  tmp = mpi_alloc( mpi_get_nlimbs(skey->p) );
  mpi_mul( tmp, skey->x, r );
  mpi_add( tmp, tmp, hash );
  mpi_mulm( s , kinv, tmp, skey->q );

  mpi_free(k);
  mpi_free(kinv);
  mpi_free(tmp);
}


/*
   Returns true if the signature composed from R and S is valid.
 */
static int
verify (gcry_mpi_t r, gcry_mpi_t s, gcry_mpi_t hash, DSA_public_key *pkey )
{
  int rc;
  gcry_mpi_t w, u1, u2, v;
  gcry_mpi_t base[3];
  gcry_mpi_t ex[3];

  if( !(mpi_cmp_ui( r, 0 ) > 0 && mpi_cmp( r, pkey->q ) < 0) )
    return 0; /* assertion	0 < r < q  failed */
  if( !(mpi_cmp_ui( s, 0 ) > 0 && mpi_cmp( s, pkey->q ) < 0) )
    return 0; /* assertion	0 < s < q  failed */

  w  = mpi_alloc( mpi_get_nlimbs(pkey->q) );
  u1 = mpi_alloc( mpi_get_nlimbs(pkey->q) );
  u2 = mpi_alloc( mpi_get_nlimbs(pkey->q) );
  v  = mpi_alloc( mpi_get_nlimbs(pkey->p) );

  /* w = s^(-1) mod q */
  mpi_invm( w, s, pkey->q );

  /* u1 = (hash * w) mod q */
  mpi_mulm( u1, hash, w, pkey->q );

  /* u2 = r * w mod q  */
  mpi_mulm( u2, r, w, pkey->q );

  /* v =  g^u1 * y^u2 mod p mod q */
  base[0] = pkey->g; ex[0] = u1;
  base[1] = pkey->y; ex[1] = u2;
  base[2] = NULL;    ex[2] = NULL;
  mpi_mulpowm( v, base, ex, pkey->p );
  mpi_fdiv_r( v, v, pkey->q );

  rc = !mpi_cmp( v, r );

  mpi_free(w);
  mpi_free(u1);
  mpi_free(u2);
  mpi_free(v);

  return rc;
}


/*********************************************
 **************  interface  ******************
 *********************************************/

gcry_err_code_t
_gcry_dsa_generate (int algo, unsigned int nbits, unsigned long dummy,
                    gcry_mpi_t *skey, gcry_mpi_t **retfactors)
{
  gpg_err_code_t err;
  DSA_secret_key sk;

  (void)algo;
  (void)dummy;

  err = generate (&sk, nbits, 0, retfactors);
  if (!err)
    {
      skey[0] = sk.p;
      skey[1] = sk.q;
      skey[2] = sk.g;
      skey[3] = sk.y;
      skey[4] = sk.x;
    }

  return err;
}


/* We don't want to break our API.  Thus we use a hack in pubkey.c to
   link directly to this function.  Note that we can't reuse the dummy
   parameter because we can't be sure that applicaions accidently pass
   a USE_E (that is for what dummy is used with RSA) to a DSA
   generation. */
gcry_err_code_t
_gcry_dsa_generate2 (int algo, unsigned int nbits, unsigned int qbits,
                     unsigned long dummy,
                     gcry_mpi_t *skey, gcry_mpi_t **retfactors)
{
  gpg_err_code_t err;
  DSA_secret_key sk;

  (void)algo;
  (void)dummy;

  err = generate (&sk, nbits, qbits, retfactors);
  if (!err)
    {
      skey[0] = sk.p;
      skey[1] = sk.q;
      skey[2] = sk.g;
      skey[3] = sk.y;
      skey[4] = sk.x;
    }

  return err;
}


gcry_err_code_t
_gcry_dsa_check_secret_key (int algo, gcry_mpi_t *skey)
{
  gcry_err_code_t err = GPG_ERR_NO_ERROR;
  DSA_secret_key sk;

  (void)algo;

  if ((! skey[0]) || (! skey[1]) || (! skey[2]) || (! skey[3]) || (! skey[4]))
    err = GPG_ERR_BAD_MPI;
  else
    {
      sk.p = skey[0];
      sk.q = skey[1];
      sk.g = skey[2];
      sk.y = skey[3];
      sk.x = skey[4];
      if (! check_secret_key (&sk))
	err = GPG_ERR_BAD_SECKEY;
    }

  return err;
}


gcry_err_code_t
_gcry_dsa_sign (int algo, gcry_mpi_t *resarr, gcry_mpi_t data, gcry_mpi_t *skey)
{
  gcry_err_code_t err = GPG_ERR_NO_ERROR;
  DSA_secret_key sk;

  (void)algo;

  if ((! data)
      || (! skey[0]) || (! skey[1]) || (! skey[2])
      || (! skey[3]) || (! skey[4]))
    err = GPG_ERR_BAD_MPI;
  else
    {
      sk.p = skey[0];
      sk.q = skey[1];
      sk.g = skey[2];
      sk.y = skey[3];
      sk.x = skey[4];
      resarr[0] = mpi_alloc (mpi_get_nlimbs (sk.p));
      resarr[1] = mpi_alloc (mpi_get_nlimbs (sk.p));
      sign (resarr[0], resarr[1], data, &sk);
    }
  return err;
}

gcry_err_code_t
_gcry_dsa_verify (int algo, gcry_mpi_t hash, gcry_mpi_t *data, gcry_mpi_t *pkey,
		  int (*cmp) (void *, gcry_mpi_t), void *opaquev)
{
  gcry_err_code_t err = GPG_ERR_NO_ERROR;
  DSA_public_key pk;

  (void)algo;
  (void)cmp;
  (void)opaquev;

  if ((! data[0]) || (! data[1]) || (! hash)
      || (! pkey[0]) || (! pkey[1]) || (! pkey[2]) || (! pkey[3]))
    err = GPG_ERR_BAD_MPI;
  else
    {
      pk.p = pkey[0];
      pk.q = pkey[1];
      pk.g = pkey[2];
      pk.y = pkey[3];
      if (! verify (data[0], data[1], hash, &pk))
	err = GPG_ERR_BAD_SIGNATURE;
    }
  return err;
}


unsigned int
_gcry_dsa_get_nbits (int algo, gcry_mpi_t *pkey)
{
  (void)algo;

  return mpi_get_nbits (pkey[0]);
}



/* 
     Self-test section.
 */

static const char *
selftest_sign_1024 (gcry_sexp_t pkey, gcry_sexp_t skey)
{
  static const char sample_data[] = 
    "(data (flags pkcs1)"
    " (hash sha1 #a0b1c2d3e4f500102030405060708090a1b2c3d4#))";
  static const char sample_data_bad[] = 
    "(data (flags pkcs1)"
    " (hash sha1 #a0b1c2d3e4f510102030405060708090a1b2c3d4#))";

  const char *errtxt = NULL;
  gcry_error_t err;
  gcry_sexp_t data = NULL;
  gcry_sexp_t data_bad = NULL;
  gcry_sexp_t sig = NULL;

  err = gcry_sexp_sscan (&data, NULL,
                         sample_data, strlen (sample_data));
  if (!err)
    err = gcry_sexp_sscan (&data_bad, NULL, 
                           sample_data_bad, strlen (sample_data_bad));
  if (err)
    {
      errtxt = "converting data failed";
      goto leave;
    }

  err = gcry_pk_sign (&sig, data, skey);
  if (err)
    {
      errtxt = "signing failed";
      goto leave;
    }
  err = gcry_pk_verify (sig, data, pkey);
  if (err)
    {
      errtxt = "verify failed";
      goto leave;
    }
  err = gcry_pk_verify (sig, data_bad, pkey);
  if (gcry_err_code (err) != GPG_ERR_BAD_SIGNATURE)
    {
      errtxt = "bad signature not detected";
      goto leave;
    }


 leave:
  gcry_sexp_release (sig);
  gcry_sexp_release (data_bad);
  gcry_sexp_release (data);
  return errtxt;
}


static gpg_err_code_t
selftests_dsa (selftest_report_func_t report)
{
  const char *what;
  const char *errtxt;
  gcry_error_t err;
  gcry_sexp_t skey = NULL;
  gcry_sexp_t pkey = NULL;

  /* Convert the S-expressions into the internal representation.  */
  what = "convert";
  err = gcry_sexp_sscan (&skey, NULL, 
                         sample_secret_key, strlen (sample_secret_key));
  if (!err)
    err = gcry_sexp_sscan (&pkey, NULL, 
                           sample_public_key, strlen (sample_public_key));
  if (err)
    {
      errtxt = gcry_strerror (err);
      goto failed;
    }

  what = "key consistency";
  err = gcry_pk_testkey (skey);
  if (err)
    {
      errtxt = gcry_strerror (err);
      goto failed;
    }

  what = "sign";
  errtxt = selftest_sign_1024 (pkey, skey);
  if (errtxt)
    goto failed;

  gcry_sexp_release (pkey);
  gcry_sexp_release (skey);
  return 0; /* Succeeded. */

 failed:
  gcry_sexp_release (pkey);
  gcry_sexp_release (skey);
  if (report)
    report ("pubkey", GCRY_PK_DSA, what, errtxt);
  return GPG_ERR_SELFTEST_FAILED;
}


/* Run a full self-test for ALGO and return 0 on success.  */
static gpg_err_code_t
run_selftests (int algo, int extended, selftest_report_func_t report)
{
  gpg_err_code_t ec;

  (void)extended;

  switch (algo)
    {
    case GCRY_PK_DSA:
      ec = selftests_dsa (report);
      break;
    default:
      ec = GPG_ERR_PUBKEY_ALGO;
      break;
        
    }
  return ec;
}




static const char *dsa_names[] =
  {
    "dsa",
    "openpgp-dsa",
    NULL,
  };

gcry_pk_spec_t _gcry_pubkey_spec_dsa =
  {
    "DSA", dsa_names, 
    "pqgy", "pqgyx", "", "rs", "pqgy",
    GCRY_PK_USAGE_SIGN,
    _gcry_dsa_generate,
    _gcry_dsa_check_secret_key,
    NULL,
    NULL,
    _gcry_dsa_sign,
    _gcry_dsa_verify,
    _gcry_dsa_get_nbits,
  };
pk_extra_spec_t _gcry_pubkey_extraspec_dsa = 
  {
    run_selftests
  };

