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

pub use ffi::fe25519;

impl Default for fe25519 {
    #[inline(always)]
    fn default() -> fe25519 {
        unsafe {core::mem::uninitialized()}
    }
}

impl fe25519 {
    #[inline]
    pub fn zero() -> fe25519 {
        let mut z = fe25519::default();
        unsafe {
            ffi::fe25519_setzero(&mut z as *mut fe25519);
        }
        z
    }

    #[inline]
    pub fn one() -> fe25519 {
        let mut z = fe25519::default();
        unsafe {
            ffi::fe25519_setone(&mut z as *mut fe25519);
        }
        z
    }

    #[inline]
    pub fn b() -> fe25519 {
        let mut z = fe25519::zero();
        unsafe {
            z.as_uint16_t[0] += 13318;
        }
        z
    }

    #[inline]
    pub fn copy(&self) -> fe25519 {
        let mut result = fe25519::default();
        unsafe {
            ffi::fe25519_cpy(&mut result as *mut fe25519, self as *const fe25519);
        }
        result
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
    pub fn unpack(bytes: &[u8]) -> fe25519 {
        assert_eq!(bytes.len(), 32);
        let mut z = fe25519::default();
        unsafe {
            ffi::fe25519_unpack(&mut z as *mut fe25519, bytes.as_ptr());
        }
        z
    }

    #[inline]
    pub fn pack(&mut self) -> [u8; 32] {
        let mut packed = [0_u8; 32];
        unsafe {
            ffi::fe25519_pack(packed.as_mut_ptr(), self as *mut fe25519);
        }
        packed
    }

    #[inline]
    pub fn iseq_vartime(&mut self, other: &mut fe25519) -> bool {
        (unsafe { ffi::fe25519_iseq_vartime(self as *mut fe25519, other as *mut fe25519) } != 0)
    }

    #[inline]
    pub fn sub(&self, rhs: &fe25519) -> fe25519 {
        let mut result = fe25519::default();
        unsafe {
            ffi::fe25519_sub(
                &mut result as *mut fe25519,
                self as *const fe25519,
                rhs as *const fe25519,
            );
        }
        result
    }

    #[inline]
    pub fn neg(&self) -> fe25519 {
        let mut result = fe25519::default();
        unsafe {
            ffi::fe25519_neg(&mut result as *mut fe25519, self as *const fe25519);
        }
        result
    }

    #[inline]
    pub fn add(&self, rhs: &fe25519) -> fe25519 {
        let mut result = fe25519::default();
        unsafe {
            ffi::fe25519_add(
                &mut result as *mut fe25519,
                self as *const fe25519,
                rhs as *const fe25519,
            );
        }
        result
    }

    #[inline]
    pub fn mul_u16(mut self, rhs: u16) -> fe25519 {
        unsafe { ffi::fe25519_mpyWith_uint16(&mut self as *mut fe25519, rhs) }
        self
    }

    #[inline]
    pub fn reduceCompletely(mut self) -> fe25519 {
        unsafe { ffi::fe25519_reduceCompletely(&mut self as *mut fe25519) }
        self
    }

    #[inline]
    pub fn mul(&self, rhs: &fe25519) -> fe25519 {
        let mut result = fe25519::default();
        unsafe {
            ffi::fe25519_mul_asm(
                &mut result as *mut fe25519,
                self as *const fe25519,
                rhs as *const fe25519,
            );
        }
        result
    }

    #[inline]
    pub fn square(&self) -> fe25519 {
        let mut result = fe25519::default();
        unsafe {
            ffi::fe25519_square_asm(&mut result as *mut fe25519, self as *const fe25519);
        }
        result
    }

    #[inline]
    pub fn invert(&self) -> fe25519 {
        let mut result = fe25519::default();
        unsafe {
            ffi::fe25519_invert(&mut result as *mut fe25519, self as *const fe25519);
        }
        result
    }
}
