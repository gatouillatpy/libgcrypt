/* secmem.h -  internal definitions for secmem
 *	Copyright (C) 2000, 2001 Free Software Foundation, Inc.
 *
 * This file is part of Libgcrypt.
 *
 * Libgcrypt is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * Libgcrypt is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA
 */

#ifndef G10_SECMEM_H
#define G10_SECMEM_H 1

void _gcry_secmem_init( size_t npool );
void _gcry_secmem_term( void );
void *_gcry_secmem_malloc( size_t size );
void *_gcry_secmem_realloc( void *a, size_t newsize );
void _gcry_secmem_free( void *a );
void _gcry_secmem_dump_stats(void);
void _gcry_secmem_set_flags( unsigned flags );
unsigned _gcry_secmem_get_flags(void);

int _gcry_private_is_secure( const void *p );

#endif /* G10_SECMEM_H */
