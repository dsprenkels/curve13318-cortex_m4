#![no_std]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

mod c_types {
    #![allow(unused)]
    pub type c_uchar = u8;
    pub type c_ushort = u16;
    pub type c_uint = u32;
    pub type c_ulong = u64;
    pub type c_ulonglong = u128;

    pub type c_char = i8;
    pub type c_short = i16;
    pub type c_int = i32;
    pub type c_long = i64;
    pub type c_longlong = i128;
}

pub mod ffi {
    include!(concat!(env!("OUT_DIR"), "/bindings.rs"));
}

impl Default for fe25519 {
    #[inline(always)]
    fn default() -> fe25519 {
        let mut z = Self::uninitialized();
        z.zero();
        z
    }
}

pub use ffi::fe25519;

impl fe25519 {
    #[inline(always)]
    pub fn uninitialized() -> fe25519 {
        unsafe { core::mem::uninitialized() }
    }

    #[inline]
    pub fn zero(&mut self) {
        unsafe {
            ffi::fe25519_setzero(self as *mut fe25519);
        }
    }

    #[inline]
    pub fn one(&mut self) {
        unsafe {
            ffi::fe25519_setone(self as *mut fe25519);
        }
    }

    #[inline]
    pub fn b(&mut self) {
        self.zero();
        unsafe {
            self.as_uint16_t[0] += 13318;
        }
    }

    #[inline]
    pub fn copy(&mut self, from: &fe25519) {
        unsafe {
            ffi::fe25519_cpy(self as *mut fe25519, from as *const fe25519);
        }
    }

    #[inline]
    pub fn cmov(mut self, input: &fe25519, condition: bool) -> fe25519 {
        unsafe {
            ffi::fe25519_cmov(
                &mut self as *mut fe25519,
                input as *const fe25519,
                i32::from(condition),
            );
        }
        self
    }

    pub fn cswap(a: &mut fe25519, b: &mut fe25519, condition: bool) {
        unsafe { ffi::fe25519_cswap(a as *mut fe25519, b as *mut fe25519, i32::from(condition)) }
    }

    #[inline]
    pub fn unpack_from(&mut self, bytes: &[u8]) {
        assert_eq!(bytes.len(), 32);
        unsafe {
            ffi::fe25519_unpack(self as *mut fe25519, bytes.as_ptr());
        }
    }

    #[inline]
    pub fn pack_into(&mut self, bytes: &mut [u8]) {
        assert_eq!(bytes.len(), 32);
        unsafe {
            ffi::fe25519_pack(bytes.as_mut_ptr(), self as *mut fe25519);
        }
    }

    #[inline]
    pub fn iseq_vartime(&mut self, other: &mut fe25519) -> bool {
        (unsafe { ffi::fe25519_iseq_vartime(self as *mut fe25519, other as *mut fe25519) } != 0)
    }

    #[inline]
    pub fn sub(&mut self, lhs: &fe25519, rhs: &fe25519) {
        unsafe {
            ffi::fe25519_sub(
                self as *mut fe25519,
                lhs as *const fe25519,
                rhs as *const fe25519,
            );
        }
    }

    #[inline]
    pub fn sub_assign(&mut self, rhs: &fe25519) {
        unsafe {
            ffi::fe25519_sub(
                self as *mut fe25519,
                self as *const fe25519,
                rhs as *const fe25519,
            );
        }
    }

    #[inline]
    pub fn sub_assign_swap(&mut self, rhs: &fe25519) {
        unsafe {
            ffi::fe25519_sub(
                self as *mut fe25519,
                rhs as *const fe25519,
                self as *const fe25519,
            );
        }
    }

    #[inline]
    pub fn neg(&self) -> fe25519 {
        let mut result = fe25519::uninitialized();
        unsafe {
            ffi::fe25519_neg(&mut result as *mut fe25519, self as *const fe25519);
        }
        result
    }

    #[inline]
    pub fn add(&mut self, lhs: &fe25519, rhs: &fe25519) {
        unsafe {
            ffi::fe25519_add_asm(
                self as *mut fe25519,
                lhs as *const fe25519,
                rhs as *const fe25519,
            );
        }
    }

    #[inline]
    pub fn add_assign(&mut self, rhs: &fe25519) {
        unsafe {
            ffi::fe25519_add_asm(
                self as *mut fe25519,
                self as *const fe25519,
                rhs as *const fe25519,
            );
        }
    }

    #[inline]
    pub fn double(&mut self) {
        unsafe {
            ffi::fe25519_add_asm(
                self as *mut fe25519,
                self as *const fe25519,
                self as *const fe25519,
            );
        }
    }

    #[inline]
    pub fn mul_u16(&mut self, rhs: u16) {
        unsafe { ffi::fe25519_mpyWith_uint16_asm(self as *mut fe25519, rhs) }
    }

    #[inline]
    pub fn reduceCompletely(&mut self) {
        unsafe { ffi::fe25519_reduceCompletely(self as *mut fe25519) }
    }

    #[inline]
    pub fn mul(&mut self, lhs: &fe25519, rhs: &fe25519) {
        unsafe {
            ffi::fe25519_mul_asm(
                self as *mut fe25519,
                lhs as *const fe25519,
                rhs as *const fe25519,
            );
        }
    }

    #[inline]
    pub fn mul_assign(&mut self, rhs: &fe25519) {
        unsafe {
            ffi::fe25519_mul_asm(
                self as *mut fe25519,
                self as *const fe25519,
                rhs as *const fe25519,
            );
        }
    }

    #[inline]
    pub fn square(&mut self, rhs: &fe25519) {
        unsafe {
            ffi::fe25519_square_asm(self as *mut fe25519, rhs as *const fe25519);
        }
    }

    #[inline]
    pub fn invert(&mut self, rhs: &fe25519) {
        unsafe {
            ffi::fe25519_invert(self as *mut fe25519, rhs as *const fe25519);
        }
    }
}
