/* elgamal.c  -  ElGamal Public Key encryption
 * Copyright (C) 1998, 2000, 2001, 2002 Free Software Foundation, Inc.
 *
 * This file is part of Libgcrypt.
 *
 * Libgcrypt is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser general Public License as
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
 *
 * For a description of the algorithm, see:
 *   Bruce Schneier: Applied Cryptography. John Wiley & Sons, 1996.
 *   ISBN 0-471-11709-9. Pages 476 ff.
 */

#include <config.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "g10lib.h"
#include "mpi.h"
#include "cipher.h"
#include "elgamal.h"

typedef struct {
    MPI p;	    /* prime */
    MPI g;	    /* group generator */
    MPI y;	    /* g^x mod p */
} ELG_public_key;


typedef struct {
    MPI p;	    /* prime */
    MPI g;	    /* group generator */
    MPI y;	    /* g^x mod p */
    MPI x;	    /* secret exponent */
} ELG_secret_key;


static void test_keys( ELG_secret_key *sk, unsigned nbits );
static MPI gen_k( MPI p );
static void generate( ELG_secret_key *sk, unsigned nbits, MPI **factors );
static int  check_secret_key( ELG_secret_key *sk );
static void do_encrypt(MPI a, MPI b, MPI input, ELG_public_key *pkey );
static void decrypt(MPI output, MPI a, MPI b, ELG_secret_key *skey );
static void sign(MPI a, MPI b, MPI input, ELG_secret_key *skey);
static int  verify(MPI a, MPI b, MPI input, ELG_public_key *pkey);


static void (*progress_cb) ( void *, int );
static void *progress_cb_data;

void
_gcry_register_pk_elg_progress ( void (*cb)( void *, int), void *cb_data )
{
    progress_cb = cb;
    progress_cb_data = cb_data;
}


static void
progress( int c )
{
    if ( progress_cb )
	progress_cb ( progress_cb_data, c );
    else
	fputc( c, stderr );
}


/****************
 * Michael Wiener's table on subgroup sizes to match field sizes
 * (floating around somewhere - Fixme: need a reference)
 */
static unsigned int
wiener_map( unsigned int n )
{
    static struct { unsigned int p_n, q_n; } t[] =
    {	/*   p	  q	 attack cost */
	{  512, 119 },	/* 9 x 10^17 */
	{  768, 145 },	/* 6 x 10^21 */
	{ 1024, 165 },	/* 7 x 10^24 */
	{ 1280, 183 },	/* 3 x 10^27 */
	{ 1536, 198 },	/* 7 x 10^29 */
	{ 1792, 212 },	/* 9 x 10^31 */
	{ 2048, 225 },	/* 8 x 10^33 */
	{ 2304, 237 },	/* 5 x 10^35 */
	{ 2560, 249 },	/* 3 x 10^37 */
	{ 2816, 259 },	/* 1 x 10^39 */
	{ 3072, 269 },	/* 3 x 10^40 */
	{ 3328, 279 },	/* 8 x 10^41 */
	{ 3584, 288 },	/* 2 x 10^43 */
	{ 3840, 296 },	/* 4 x 10^44 */
	{ 4096, 305 },	/* 7 x 10^45 */
	{ 4352, 313 },	/* 1 x 10^47 */
	{ 4608, 320 },	/* 2 x 10^48 */
	{ 4864, 328 },	/* 2 x 10^49 */
	{ 5120, 335 },	/* 3 x 10^50 */
	{ 0, 0 }
    };
    int i;

    for(i=0; t[i].p_n; i++ )  {
	if( n <= t[i].p_n )
	    return t[i].q_n;
    }
    /* not in table - use some arbitrary high number ;-) */
    return  n / 8 + 200;
}

static void
test_keys( ELG_secret_key *sk, unsigned nbits )
{
    ELG_public_key pk;
    MPI test = gcry_mpi_new ( 0 );
    MPI out1_a = gcry_mpi_new ( nbits );
    MPI out1_b = gcry_mpi_new ( nbits );
    MPI out2 = gcry_mpi_new ( nbits );

    pk.p = sk->p;
    pk.g = sk->g;
    pk.y = sk->y;

    gcry_mpi_randomize( test, nbits, GCRY_WEAK_RANDOM );

    do_encrypt( out1_a, out1_b, test, &pk );
    decrypt( out2, out1_a, out1_b, sk );
    if( mpi_cmp( test, out2 ) )
	log_fatal("ElGamal operation: encrypt, decrypt failed\n");

    sign( out1_a, out1_b, test, sk );
    if( !verify( out1_a, out1_b, test, &pk ) )
	log_fatal("ElGamal operation: sign, verify failed\n");

    gcry_mpi_release ( test );
    gcry_mpi_release ( out1_a );
    gcry_mpi_release ( out1_b );
    gcry_mpi_release ( out2 );
}


/****************
 * generate a random secret exponent k from prime p, so
 * that k is relatively prime to p-1
 */
static MPI
gen_k( MPI p )
{
    MPI k = mpi_alloc_secure( 0 );
    MPI temp = mpi_alloc( mpi_get_nlimbs(p) );
    MPI p_1 = mpi_copy(p);
    unsigned int orig_nbits = mpi_get_nbits(p);
    unsigned int nbits, nbytes;
    char *rndbuf = NULL;

    /* IMO using a k much lesser than p is sufficient and it greatly
     * improves the encryption performance.  We use Wiener's table
     * and add a large safety margin.
     */
    nbits = wiener_map( orig_nbits ) * 3 / 2;
    if( nbits >= orig_nbits )
	BUG();

    nbytes = (nbits+7)/8;
    if( DBG_CIPHER )
	log_debug("choosing a random k ");
    mpi_sub_ui( p_1, p, 1);
    for(;;) {
	if( !rndbuf || nbits < 32 ) {
	    gcry_free(rndbuf);
	    rndbuf = gcry_random_bytes_secure( nbytes, GCRY_STRONG_RANDOM );
	}
	else { /* change only some of the higher bits */
	    /* we could improve this by directly requesting more memory
	     * at the first call to get_random_bytes() and use this the here
	     * maybe it is easier to do this directly in random.c
	     * Anyway, it is highly inlikely that we will ever reach this code
	     */
	    char *pp = gcry_random_bytes_secure( 4, GCRY_STRONG_RANDOM );
	    memcpy( rndbuf, pp, 4 );
	    gcry_free(pp);
	    log_debug("gen_k: tsss, never expected to reach this\n");
	}
	_gcry_mpi_set_buffer( k, rndbuf, nbytes, 0 );

	for(;;) {
	    /* Hmm, actually we don't need this step here
	     * because we use k much smaller than p - we do it anyway
	     * just in case the keep on adding a one to k ;) */
	    if( !(mpi_cmp( k, p_1 ) < 0) ) {  /* check: k < (p-1) */
		if( DBG_CIPHER )
		    progress('+');
		break; /* no  */
	    }
	    if( !(mpi_cmp_ui( k, 0 ) > 0) ) { /* check: k > 0 */
		if( DBG_CIPHER )
		    progress('-');
		break; /* no */
	    }
	    if( gcry_mpi_gcd( temp, k, p_1 ) )
		goto found;  /* okay, k is relatively prime to (p-1) */
	    mpi_add_ui( k, k, 1 );
	    if( DBG_CIPHER )
		progress('.');
	}
    }
  found:
    gcry_free(rndbuf);
    if( DBG_CIPHER )
	progress('\n');
    mpi_free(p_1);
    mpi_free(temp);

    return k;
}

/****************
 * Generate a key pair with a key of size NBITS
 * Returns: 2 structures filles with all needed values
 *	    and an array with n-1 factors of (p-1)
 */
static void
generate(  ELG_secret_key *sk, unsigned int nbits, MPI **ret_factors )
{
    MPI p;    /* the prime */
    MPI p_min1;
    MPI g;
    MPI x;    /* the secret exponent */
    MPI y;
    MPI temp;
    unsigned int qbits;
    unsigned int xbits;
    byte *rndbuf;

    p_min1 = gcry_mpi_new ( nbits );
    temp   = gcry_mpi_new( nbits );
    qbits = wiener_map( nbits );
    if( qbits & 1 ) /* better have a even one */
	qbits++;
    g = mpi_alloc(1);
    p = _gcry_generate_elg_prime( 0, nbits, qbits, g, ret_factors );
    mpi_sub_ui(p_min1, p, 1);


    /* select a random number which has these properties:
     *	 0 < x < p-1
     * This must be a very good random number because this is the
     * secret part.  The prime is public and may be shared anyway,
     * so a random generator level of 1 is used for the prime.
     *
     * I don't see a reason to have a x of about the same size
     * as the p.  It should be sufficient to have one about the size
     * of q or the later used k plus a large safety margin. Decryption
     * will be much faster with such an x.
     */
    xbits = qbits * 3 / 2;
    if( xbits >= nbits )
	BUG();
    x = gcry_mpi_snew ( xbits );
    if( DBG_CIPHER )
	log_debug("choosing a random x of size %u", xbits );
    rndbuf = NULL;
    do {
	if( DBG_CIPHER )
	    progress('.');
	if( rndbuf ) { /* change only some of the higher bits */
	    if( xbits < 16 ) {/* should never happen ... */
		gcry_free(rndbuf);
		rndbuf = gcry_random_bytes_secure( (xbits+7)/8,
						   GCRY_VERY_STRONG_RANDOM );
	    }
	    else {
		char *r = gcry_random_bytes_secure( 2,
						   GCRY_VERY_STRONG_RANDOM );
		memcpy(rndbuf, r, 2 );
		gcry_free(r);
	    }
	}
	else {
	    rndbuf = gcry_random_bytes_secure( (xbits+7)/8,
					       GCRY_VERY_STRONG_RANDOM );
	}
	_gcry_mpi_set_buffer( x, rndbuf, (xbits+7)/8, 0 );
	mpi_clear_highbit( x, xbits+1 );
    } while( !( mpi_cmp_ui( x, 0 )>0 && mpi_cmp( x, p_min1 )<0 ) );
    gcry_free(rndbuf);

    y = gcry_mpi_new (nbits);
    gcry_mpi_powm( y, g, x, p );

    if( DBG_CIPHER ) {
	progress('\n');
	log_mpidump("elg  p= ", p );
	log_mpidump("elg  g= ", g );
	log_mpidump("elg  y= ", y );
	log_mpidump("elg  x= ", x );
    }

    /* copy the stuff to the key structures */
    sk->p = p;
    sk->g = g;
    sk->y = y;
    sk->x = x;

    /* now we can test our keys (this should never fail!) */
    test_keys( sk, nbits - 64 );

    gcry_mpi_release ( p_min1 );
    gcry_mpi_release ( temp   );
}


/****************
 * Test whether the secret key is valid.
 * Returns: if this is a valid key.
 */
static int
check_secret_key( ELG_secret_key *sk )
{
    int rc;
    MPI y = mpi_alloc( mpi_get_nlimbs(sk->y) );

    gcry_mpi_powm( y, sk->g, sk->x, sk->p );
    rc = !mpi_cmp( y, sk->y );
    mpi_free( y );
    return rc;
}


static void
do_encrypt(MPI a, MPI b, MPI input, ELG_public_key *pkey )
{
    MPI k;

    /* Note: maybe we should change the interface, so that it
     * is possible to check that input is < p and return an
     * error code.
     */

    k = gen_k( pkey->p );
    gcry_mpi_powm( a, pkey->g, k, pkey->p );
    /* b = (y^k * input) mod p
     *	 = ((y^k mod p) * (input mod p)) mod p
     * and because input is < p
     *	 = ((y^k mod p) * input) mod p
     */
    gcry_mpi_powm( b, pkey->y, k, pkey->p );
    gcry_mpi_mulm( b, b, input, pkey->p );
  #if 0
    if( DBG_CIPHER ) {
	log_mpidump("elg encrypted y= ", pkey->y);
	log_mpidump("elg encrypted p= ", pkey->p);
	log_mpidump("elg encrypted k= ", k);
	log_mpidump("elg encrypted M= ", input);
	log_mpidump("elg encrypted a= ", a);
	log_mpidump("elg encrypted b= ", b);
    }
  #endif
    mpi_free(k);
}




static void
decrypt(MPI output, MPI a, MPI b, ELG_secret_key *skey )
{
    MPI t1 = mpi_alloc_secure( mpi_get_nlimbs( skey->p ) );

    /* output = b/(a^x) mod p */
    gcry_mpi_powm( t1, a, skey->x, skey->p );
    mpi_invm( t1, t1, skey->p );
    mpi_mulm( output, b, t1, skey->p );
  #if 0
    if( DBG_CIPHER ) {
	log_mpidump("elg decrypted x= ", skey->x);
	log_mpidump("elg decrypted p= ", skey->p);
	log_mpidump("elg decrypted a= ", a);
	log_mpidump("elg decrypted b= ", b);
	log_mpidump("elg decrypted M= ", output);
    }
  #endif
    mpi_free(t1);
}


/****************
 * Make an Elgamal signature out of INPUT
 */

static void
sign(MPI a, MPI b, MPI input, ELG_secret_key *skey )
{
    MPI k;
    MPI t   = mpi_alloc( mpi_get_nlimbs(a) );
    MPI inv = mpi_alloc( mpi_get_nlimbs(a) );
    MPI p_1 = mpi_copy(skey->p);

   /*
    * b = (t * inv) mod (p-1)
    * b = (t * inv(k,(p-1),(p-1)) mod (p-1)
    * b = (((M-x*a) mod (p-1)) * inv(k,(p-1),(p-1))) mod (p-1)
    *
    */
    mpi_sub_ui(p_1, p_1, 1);
    k = gen_k( skey->p );
    gcry_mpi_powm( a, skey->g, k, skey->p );
    mpi_mul(t, skey->x, a );
    mpi_subm(t, input, t, p_1 );
    mpi_invm(inv, k, p_1 );
    mpi_mulm(b, t, inv, p_1 );

  #if 0
    if( DBG_CIPHER ) {
	log_mpidump("elg sign p= ", skey->p);
	log_mpidump("elg sign g= ", skey->g);
	log_mpidump("elg sign y= ", skey->y);
	log_mpidump("elg sign x= ", skey->x);
	log_mpidump("elg sign k= ", k);
	log_mpidump("elg sign M= ", input);
	log_mpidump("elg sign a= ", a);
	log_mpidump("elg sign b= ", b);
    }
  #endif
    mpi_free(k);
    mpi_free(t);
    mpi_free(inv);
    mpi_free(p_1);
}


/****************
 * Returns true if the signature composed of A and B is valid.
 */
static int
verify(MPI a, MPI b, MPI input, ELG_public_key *pkey )
{
    int rc;
    MPI t1;
    MPI t2;
    MPI base[4];
    MPI exp[4];

    if( !(mpi_cmp_ui( a, 0 ) > 0 && mpi_cmp( a, pkey->p ) < 0) )
	return 0; /* assertion	0 < a < p  failed */

    t1 = mpi_alloc( mpi_get_nlimbs(a) );
    t2 = mpi_alloc( mpi_get_nlimbs(a) );

  #if 0
    /* t1 = (y^a mod p) * (a^b mod p) mod p */
    gcry_mpi_powm( t1, pkey->y, a, pkey->p );
    gcry_mpi_powm( t2, a, b, pkey->p );
    mpi_mulm( t1, t1, t2, pkey->p );

    /* t2 = g ^ input mod p */
    gcry_mpi_powm( t2, pkey->g, input, pkey->p );

    rc = !mpi_cmp( t1, t2 );
  #elif 0
    /* t1 = (y^a mod p) * (a^b mod p) mod p */
    base[0] = pkey->y; exp[0] = a;
    base[1] = a;       exp[1] = b;
    base[2] = NULL;    exp[2] = NULL;
    mpi_mulpowm( t1, base, exp, pkey->p );

    /* t2 = g ^ input mod p */
    gcry_mpi_powm( t2, pkey->g, input, pkey->p );

    rc = !mpi_cmp( t1, t2 );
  #else
    /* t1 = g ^ - input * y ^ a * a ^ b  mod p */
    mpi_invm(t2, pkey->g, pkey->p );
    base[0] = t2     ; exp[0] = input;
    base[1] = pkey->y; exp[1] = a;
    base[2] = a;       exp[2] = b;
    base[3] = NULL;    exp[3] = NULL;
    mpi_mulpowm( t1, base, exp, pkey->p );
    rc = !mpi_cmp_ui( t1, 1 );

  #endif

    mpi_free(t1);
    mpi_free(t2);
    return rc;
}

/*********************************************
 **************  interface  ******************
 *********************************************/

int
_gcry_elg_generate( int algo, unsigned nbits, MPI *skey, MPI **retfactors )
{
    ELG_secret_key sk;

    if( !is_ELGAMAL(algo) )
	return GCRYERR_INV_PK_ALGO;

    generate( &sk, nbits, retfactors );
    skey[0] = sk.p;
    skey[1] = sk.g;
    skey[2] = sk.y;
    skey[3] = sk.x;
    return 0;
}


int
_gcry_elg_check_secret_key( int algo, MPI *skey )
{
    ELG_secret_key sk;

    if( !is_ELGAMAL(algo) )
	return GCRYERR_INV_PK_ALGO;
    if( !skey[0] || !skey[1] || !skey[2] || !skey[3] )
	return GCRYERR_BAD_MPI;

    sk.p = skey[0];
    sk.g = skey[1];
    sk.y = skey[2];
    sk.x = skey[3];
    if( !check_secret_key( &sk ) )
	return GCRYERR_BAD_SECRET_KEY;

    return 0;
}



int
_gcry_elg_encrypt( int algo, MPI *resarr, MPI data, MPI *pkey )
{
    ELG_public_key pk;

    if( !is_ELGAMAL(algo) )
	return GCRYERR_INV_PK_ALGO;
    if( !data || !pkey[0] || !pkey[1] || !pkey[2] )
	return GCRYERR_BAD_MPI;

    pk.p = pkey[0];
    pk.g = pkey[1];
    pk.y = pkey[2];
    resarr[0] = mpi_alloc( mpi_get_nlimbs( pk.p ) );
    resarr[1] = mpi_alloc( mpi_get_nlimbs( pk.p ) );
    do_encrypt( resarr[0], resarr[1], data, &pk );
    return 0;
}

int
_gcry_elg_decrypt( int algo, MPI *result, MPI *data, MPI *skey )
{
    ELG_secret_key sk;

    if( !is_ELGAMAL(algo) )
	return GCRYERR_INV_PK_ALGO;
    if( !data[0] || !data[1]
	|| !skey[0] || !skey[1] || !skey[2] || !skey[3] )
	return GCRYERR_BAD_MPI;

    sk.p = skey[0];
    sk.g = skey[1];
    sk.y = skey[2];
    sk.x = skey[3];
    *result = mpi_alloc_secure( mpi_get_nlimbs( sk.p ) );
    decrypt( *result, data[0], data[1], &sk );
    return 0;
}

int
_gcry_elg_sign( int algo, MPI *resarr, MPI data, MPI *skey )
{
    ELG_secret_key sk;

    if( !is_ELGAMAL(algo) )
	return GCRYERR_INV_PK_ALGO;
    if( !data || !skey[0] || !skey[1] || !skey[2] || !skey[3] )
	return GCRYERR_BAD_MPI;

    sk.p = skey[0];
    sk.g = skey[1];
    sk.y = skey[2];
    sk.x = skey[3];
    resarr[0] = mpi_alloc( mpi_get_nlimbs( sk.p ) );
    resarr[1] = mpi_alloc( mpi_get_nlimbs( sk.p ) );
    sign( resarr[0], resarr[1], data, &sk );
    return 0;
}

int
_gcry_elg_verify( int algo, MPI hash, MPI *data, MPI *pkey,
		    int (*cmp)(void *, MPI), void *opaquev )
{
    ELG_public_key pk;

    if( !is_ELGAMAL(algo) )
	return GCRYERR_INV_PK_ALGO;
    if( !data[0] || !data[1] || !hash
	|| !pkey[0] || !pkey[1] || !pkey[2] )
	return GCRYERR_BAD_MPI;

    pk.p = pkey[0];
    pk.g = pkey[1];
    pk.y = pkey[2];
    if( !verify( data[0], data[1], hash, &pk ) )
	return GCRYERR_BAD_SIGNATURE;
    return 0;
}



unsigned int
_gcry_elg_get_nbits( int algo, MPI *pkey )
{
    if( !is_ELGAMAL(algo) )
	return 0;
    return mpi_get_nbits( pkey[0] );
}


/****************
 * Return some information about the algorithm.  We need algo here to
 * distinguish different flavors of the algorithm.
 * Returns: A pointer to string describing the algorithm or NULL if
 *	    the ALGO is invalid.
 * Usage: Bit 0 set : allows signing
 *	      1 set : allows encryption
 * NOTE: This function allows signing also for ELG-E, which is not
 * okay but a bad hack to allow to work with old gpg keys. The real check
 * is done in the gnupg ocde depending on the packet version.
 */
const char *
_gcry_elg_get_info( int algo, int *npkey, int *nskey, int *nenc, int *nsig,
							 int *use )
{
    *npkey = 3;
    *nskey = 4;
    *nenc = 2;
    *nsig = 2;

    switch( algo ) {
      case GCRY_PK_ELG:
	*use = GCRY_PK_USAGE_SIGN|GCRY_PK_USAGE_ENCR;
	return "ELG";
      case GCRY_PK_ELG_E:
	*use = GCRY_PK_USAGE_SIGN|GCRY_PK_USAGE_ENCR;
	return "ELG-E";
      default: *use = 0; return NULL;
    }
}


