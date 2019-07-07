#![feature(asm)]
#![no_main]
#![no_std]

extern crate fe25519_sys;
extern crate panic_semihosting;

use cortex_m::peripheral::Peripherals;
use cortex_m_rt::entry;
use cortex_m_semihosting::{hprint, hprintln};
use fe25519_sys::*;

type GE = (fe25519, fe25519, fe25519);

const B: u16 = 13318;

/// Dump a `fe25519` element to `HStdout`.
///
/// `z` is mut because it will be reduced in-place.
#[allow(unused)]
fn dump_fe25519(name: &'static str, z: &mut fe25519) {
    hprintln!("{}: {:?}", name, z.pack()).unwrap();
}

/// Dump a group element to `HStdout`.
///
/// `p` is mut because its coordinates will be reduced in-place.
#[allow(unused)]
fn dump_ge(name: &'static str, p: &mut GE) {
    let (mut x, mut y, mut z) = p;
    hprintln!(
        "{}:
    {:?}
    {:?}
    {:?}",
        name,
        x.pack(),
        y.pack(),
        z.pack()
    )
    .unwrap();
}

fn ge_double(p: &GE) -> GE {
    let &(x, y, z) = p;

    let mut t0;
    let t1;
    let mut t2;
    let mut t3;
    let mut x3;
    let mut y3;
    let mut z3;

    t0 = fe25519::square(&x); //  1.
    t1 = fe25519::square(&y); //  2.
    t2 = fe25519::square(&z); //  3.
    t3 = fe25519::mul(&x, &y); //  4.
    t3 = fe25519::add(&t3, &t3); //  5.
    z3 = fe25519::mul(&x, &z); //  6.
    z3 = fe25519::add(&z3, &z3); //  7.
    y3 = fe25519::mul_u16(t2.copy(), B); //  8.
    y3 = fe25519::sub(&y3, &z3); //  9.
    y3 = fe25519::mul_u16(y3, 3); // 11.
    x3 = fe25519::sub(&t1, &y3); // 12.
    y3 = fe25519::add(&t1, &y3); // 13.
    y3 = fe25519::mul(&x3, &y3); // 14.
    x3 = fe25519::mul(&x3, &t3); // 15.
    t2 = fe25519::mul_u16(t2, 3); // 17.
    z3 = fe25519::mul_u16(z3, B); // 18.
    z3 = fe25519::sub(&z3, &t2); // 19.
    z3 = fe25519::sub(&z3, &t0); // 20.
    z3 = fe25519::mul_u16(z3, 3); // 22.
    t0 = fe25519::mul_u16(t0, 3); // 24.
    t0 = fe25519::sub(&t0, &t2); // 25.
    t0 = fe25519::mul(&t0, &z3); // 26.
    y3 = fe25519::add(&y3, &t0); // 27.
    t0 = fe25519::mul(&y, &z); // 28.
    t0 = fe25519::add(&t0, &t0); // 29.
    z3 = fe25519::mul(&t0, &z3); // 30.
    x3 = fe25519::sub(&x3, &z3); // 31.
    z3 = fe25519::mul(&t0, &t1); // 32.
    z3 = fe25519::mul_u16(z3, 4); // 34

    (x3, y3, z3)
}

fn ge_add(p1: &GE, p2: &GE) -> GE {
    let &(x1, y1, z1) = p1;
    let &(x2, y2, z2) = p2;

    let mut t0;
    let mut t1;
    let mut t2;
    let mut t4;
    let mut t3;
    let mut x3;
    let mut y3;
    let mut z3;

    t0 = fe25519::mul(&x1, &x2); //  1.
    t1 = fe25519::mul(&y1, &y2); //  2.
    t2 = fe25519::mul(&z1, &z2); //  3.
    t3 = fe25519::add(&x1, &y1); //  4.
    t4 = fe25519::add(&x2, &y2); //  5.
    t3 = fe25519::mul(&t3, &t4); //  6.
    t4 = fe25519::add(&t0, &t1); //  7.
    t3 = fe25519::sub(&t3, &t4); //  8.
    t4 = fe25519::add(&y1, &z1); //  9.
    x3 = fe25519::add(&y2, &z2); // 10.
    t4 = fe25519::mul(&t4, &x3); // 11.
    x3 = fe25519::add(&t1, &t2); // 12.
    t4 = fe25519::sub(&t4, &x3); // 13.
    x3 = fe25519::add(&x1, &z1); // 14.
    y3 = fe25519::add(&x2, &z2); // 15.
    x3 = fe25519::mul(&x3, &y3); // 16.
    y3 = fe25519::add(&t0, &t2); // 17.
    y3 = fe25519::sub(&x3, &y3); // 18.
    z3 = fe25519::mul_u16(t2.copy(), B); // 19.
    x3 = fe25519::sub(&y3, &z3); // 20.
    x3 = fe25519::mul_u16(x3, 3); // 22.
    z3 = fe25519::sub(&t1, &x3); // 23.
    x3 = fe25519::add(&t1, &x3); // 24.
    y3 = fe25519::mul_u16(y3, B); // 25.
    t2 = fe25519::mul_u16(t2, 3); // 27.
    y3 = fe25519::sub(&y3, &t2); // 28.
    y3 = fe25519::sub(&y3, &t0); // 29.
    t1 = fe25519::add(&y3, &y3); // 30.
    y3 = fe25519::add(&t1, &y3); // 31.
    t0 = fe25519::mul_u16(t0, 3); // 33.
    t0 = fe25519::sub(&t0, &t2); // 34.
    t1 = fe25519::mul(&t4, &y3); // 35.
    t2 = fe25519::mul(&t0, &y3); // 36.
    y3 = fe25519::mul(&x3, &z3); // 37.
    y3 = fe25519::add(&y3, &t2); // 38.
    x3 = fe25519::mul(&t3, &x3); // 39.
    x3 = fe25519::sub(&x3, &t1); // 40.
    z3 = fe25519::mul(&t4, &z3); // 41.
    t1 = fe25519::mul(&t3, &t0); // 42.
    z3 = fe25519::add(&z3, &t1); // 43.

    (x3, y3, z3)
}

/// Decode the key bytes into windows and ripple the subtraction carry
fn compute_windows(e: &[u8; 32]) -> ([u8; 51], u8) {
    let mut w = [0; 51];
    w[50] = e[0] & 0x1F;
    w[49] = ((e[1] << 3) | (e[0] >> 5)) & 0x1F;
    w[49] += ((w[50] >> 5) ^ (w[50] >> 4)) & 0x1;
    w[48] = (e[1] >> 2) & 0x1F;
    w[48] += ((w[49] >> 5) ^ (w[49] >> 4)) & 0x1;
    w[47] = ((e[2] << 1) | (e[1] >> 7)) & 0x1F;
    w[47] += ((w[48] >> 5) ^ (w[48] >> 4)) & 0x1;
    w[46] = ((e[3] << 4) | (e[2] >> 4)) & 0x1F;
    w[46] += ((w[47] >> 5) ^ (w[47] >> 4)) & 0x1;
    w[45] = (e[3] >> 1) & 0x1F;
    w[45] += ((w[46] >> 5) ^ (w[46] >> 4)) & 0x1;
    w[44] = ((e[4] << 2) | (e[3] >> 6)) & 0x1F;
    w[44] += ((w[45] >> 5) ^ (w[45] >> 4)) & 0x1;
    w[43] = (e[4] >> 3) & 0x1F;
    w[43] += ((w[44] >> 5) ^ (w[44] >> 4)) & 0x1;
    w[42] = e[5] & 0x1F;
    w[42] += ((w[43] >> 5) ^ (w[43] >> 4)) & 0x1;
    w[41] = ((e[6] << 3) | (e[5] >> 5)) & 0x1F;
    w[41] += ((w[42] >> 5) ^ (w[42] >> 4)) & 0x1;
    w[40] = (e[6] >> 2) & 0x1F;
    w[40] += ((w[41] >> 5) ^ (w[41] >> 4)) & 0x1;
    w[39] = ((e[7] << 1) | (e[6] >> 7)) & 0x1F;
    w[39] += ((w[40] >> 5) ^ (w[40] >> 4)) & 0x1;
    w[38] = ((e[8] << 4) | (e[7] >> 4)) & 0x1F;
    w[38] += ((w[39] >> 5) ^ (w[39] >> 4)) & 0x1;
    w[37] = (e[8] >> 1) & 0x1F;
    w[37] += ((w[38] >> 5) ^ (w[38] >> 4)) & 0x1;
    w[36] = ((e[9] << 2) | (e[8] >> 6)) & 0x1F;
    w[36] += ((w[37] >> 5) ^ (w[37] >> 4)) & 0x1;
    w[35] = (e[9] >> 3) & 0x1F;
    w[35] += ((w[36] >> 5) ^ (w[36] >> 4)) & 0x1;
    w[34] = e[10] & 0x1F;
    w[34] += ((w[35] >> 5) ^ (w[35] >> 4)) & 0x1;
    w[33] = ((e[11] << 3) | (e[10] >> 5)) & 0x1F;
    w[33] += ((w[34] >> 5) ^ (w[34] >> 4)) & 0x1;
    w[32] = (e[11] >> 2) & 0x1F;
    w[32] += ((w[33] >> 5) ^ (w[33] >> 4)) & 0x1;
    w[31] = ((e[12] << 1) | (e[11] >> 7)) & 0x1F;
    w[31] += ((w[32] >> 5) ^ (w[32] >> 4)) & 0x1;
    w[30] = ((e[13] << 4) | (e[12] >> 4)) & 0x1F;
    w[30] += ((w[31] >> 5) ^ (w[31] >> 4)) & 0x1;
    w[29] = (e[13] >> 1) & 0x1F;
    w[29] += ((w[30] >> 5) ^ (w[30] >> 4)) & 0x1;
    w[28] = ((e[14] << 2) | (e[13] >> 6)) & 0x1F;
    w[28] += ((w[29] >> 5) ^ (w[29] >> 4)) & 0x1;
    w[27] = (e[14] >> 3) & 0x1F;
    w[27] += ((w[28] >> 5) ^ (w[28] >> 4)) & 0x1;
    w[26] = e[15] & 0x1F;
    w[26] += ((w[27] >> 5) ^ (w[27] >> 4)) & 0x1;
    w[25] = ((e[16] << 3) | (e[15] >> 5)) & 0x1F;
    w[25] += ((w[26] >> 5) ^ (w[26] >> 4)) & 0x1;
    w[24] = (e[16] >> 2) & 0x1F;
    w[24] += ((w[25] >> 5) ^ (w[25] >> 4)) & 0x1;
    w[23] = ((e[17] << 1) | (e[16] >> 7)) & 0x1F;
    w[23] += ((w[24] >> 5) ^ (w[24] >> 4)) & 0x1;
    w[22] = ((e[18] << 4) | (e[17] >> 4)) & 0x1F;
    w[22] += ((w[23] >> 5) ^ (w[23] >> 4)) & 0x1;
    w[21] = (e[18] >> 1) & 0x1F;
    w[21] += ((w[22] >> 5) ^ (w[22] >> 4)) & 0x1;
    w[20] = ((e[19] << 2) | (e[18] >> 6)) & 0x1F;
    w[20] += ((w[21] >> 5) ^ (w[21] >> 4)) & 0x1;
    w[19] = (e[19] >> 3) & 0x1F;
    w[19] += ((w[20] >> 5) ^ (w[20] >> 4)) & 0x1;
    w[18] = e[20] & 0x1F;
    w[18] += ((w[19] >> 5) ^ (w[19] >> 4)) & 0x1;
    w[17] = ((e[21] << 3) | (e[20] >> 5)) & 0x1F;
    w[17] += ((w[18] >> 5) ^ (w[18] >> 4)) & 0x1;
    w[16] = (e[21] >> 2) & 0x1F;
    w[16] += ((w[17] >> 5) ^ (w[17] >> 4)) & 0x1;
    w[15] = ((e[22] << 1) | (e[21] >> 7)) & 0x1F;
    w[15] += ((w[16] >> 5) ^ (w[16] >> 4)) & 0x1;
    w[14] = ((e[23] << 4) | (e[22] >> 4)) & 0x1F;
    w[14] += ((w[15] >> 5) ^ (w[15] >> 4)) & 0x1;
    w[13] = (e[23] >> 1) & 0x1F;
    w[13] += ((w[14] >> 5) ^ (w[14] >> 4)) & 0x1;
    w[12] = ((e[24] << 2) | (e[23] >> 6)) & 0x1F;
    w[12] += ((w[13] >> 5) ^ (w[13] >> 4)) & 0x1;
    w[11] = (e[24] >> 3) & 0x1F;
    w[11] += ((w[12] >> 5) ^ (w[12] >> 4)) & 0x1;
    w[10] = e[25] & 0x1F;
    w[10] += ((w[11] >> 5) ^ (w[11] >> 4)) & 0x1;
    w[9] = ((e[26] << 3) | (e[25] >> 5)) & 0x1F;
    w[9] += ((w[10] >> 5) ^ (w[10] >> 4)) & 0x1;
    w[8] = (e[26] >> 2) & 0x1F;
    w[8] += ((w[9] >> 5) ^ (w[9] >> 4)) & 0x1;
    w[7] = ((e[27] << 1) | (e[26] >> 7)) & 0x1F;
    w[7] += ((w[8] >> 5) ^ (w[8] >> 4)) & 0x1;
    w[6] = ((e[28] << 4) | (e[27] >> 4)) & 0x1F;
    w[6] += ((w[7] >> 5) ^ (w[7] >> 4)) & 0x1;
    w[5] = (e[28] >> 1) & 0x1F;
    w[5] += ((w[6] >> 5) ^ (w[6] >> 4)) & 0x1;
    w[4] = ((e[29] << 2) | (e[28] >> 6)) & 0x1F;
    w[4] += ((w[5] >> 5) ^ (w[5] >> 4)) & 0x1;
    w[3] = (e[29] >> 3) & 0x1F;
    w[3] += ((w[4] >> 5) ^ (w[4] >> 4)) & 0x1;
    w[2] = e[30] & 0x1F;
    w[2] += ((w[3] >> 5) ^ (w[3] >> 4)) & 0x1;
    w[1] = ((e[31] << 3) | (e[30] >> 5)) & 0x1F;
    w[1] += ((w[2] >> 5) ^ (w[2] >> 4)) & 0x1;
    w[0] = (e[31] >> 2) & 0x1F;
    w[0] += ((w[1] >> 5) ^ (w[1] >> 4)) & 0x1;
    let zeroth_window = ((w[0] >> 5) ^ (w[0] >> 4)) & 0x1;
    (w, zeroth_window)
}

fn is_valid_affine_point(x: &fe25519, y: &fe25519) -> bool {
    let b = &fe25519::b();
    let mut lhs = y.square(); // y^2
    let rhs = x.square(); // x^2
    let rhs = rhs.mul(x); // x^3
    let rhs = rhs.sub(x); // x^3 - x
    let rhs = rhs.sub(x); // x^3 - 2*x
    let rhs = rhs.sub(x); // x^3 - 3*x
    let mut rhs = rhs.add(b); // x^3 - 3*x + b
    lhs.iseq_vartime(&mut rhs)
}

// Do the table precomputation
fn precompute_table(p: &GE) -> [GE; 16] {
    let mut ptable = [GE::default(); 16];
    ptable[0] = *p;
    ptable[1] = ge_double(&ptable[0]);
    ptable[2] = ge_add(&ptable[1], &ptable[0]);
    ptable[3] = ge_double(&ptable[1]);
    ptable[4] = ge_add(&ptable[3], &ptable[0]);
    ptable[5] = ge_double(&ptable[2]);
    ptable[6] = ge_add(&ptable[5], &ptable[0]);
    ptable[7] = ge_double(&ptable[3]);
    ptable[8] = ge_add(&ptable[7], &ptable[0]);
    ptable[9] = ge_double(&ptable[4]);
    ptable[10] = ge_add(&ptable[9], &ptable[0]);
    ptable[11] = ge_double(&ptable[5]);
    ptable[12] = ge_add(&ptable[11], &ptable[0]);
    ptable[13] = ge_double(&ptable[6]);
    ptable[14] = ge_add(&ptable[13], &ptable[0]);
    ptable[15] = ge_double(&ptable[7]);
    ptable
}

/// Compute the actual index to use in the precomputed group element table
///
/// Our lookup table is one-based indexed. The neutral element is not stored
/// in `ptable`, but written by `select`. The mapping from `bits` to `idx`
/// is defined by the following:
///
/// compute_idx :: Word5 -> Word5
/// compute_idx bits
///   |  0 <= bits < 16 = bits - 1  // sign is (+)
///   | 16 <= bits < 32 = ~bits     // sign is (-)
fn compute_ptable_idx(bits: u8) -> u8 {
    let sign = (bits >> 4) & 0x1;
    let signmask = sign.wrapping_neg();
    let lhs = (bits.wrapping_sub(1)) & !signmask;
    let rhs = !bits & signmask;
    (lhs | rhs) & 0x1F
}

fn select(select_idx: usize, ptable: &[GE; 16]) -> GE {
    let mut r_x = fe25519::zero();
    let mut r_y = fe25519::zero();
    let mut r_z = fe25519::zero();
    for (scan_idx, (p_x, p_y, p_z)) in ptable.iter().enumerate() {
        let condition = scan_idx == select_idx;
        r_x = r_x.cmov(p_x, condition);
        r_y = r_y.cmov(p_y, condition);
        r_z = r_z.cmov(p_z, condition);
    }
    r_y = r_y.cmov(&fe25519::one(), select_idx == 31);
    (r_x, r_y, r_z)
}

fn ladder(mut q: GE, windows: &[u8; 51], ptable: &[GE; 16]) -> GE {
    for idx in 0..51 {
        for _ in 0..5 {
            // Double
            q = ge_double(&q);
        }
        // And add
        let w = windows[idx];
        let table_idx = compute_ptable_idx(w);
        let (x_p, mut y_p, z_p) = select(usize::from(table_idx), ptable);
        let mut y_p_neg = y_p.neg();
        let sign = (w >> 4) & 0x1;
        fe25519::cswap(&mut y_p, &mut y_p_neg, sign != 0);
        q = ge_add(&q, &(x_p, y_p, z_p));
    }
    q
}

#[inline(never)]
fn scalarmult(p_bytes: &[u8; 64], key: &[u8; 32]) -> [u8; 64] {
    let p_x = fe25519::unpack(&p_bytes[0..32]);
    let p_y = fe25519::unpack(&p_bytes[32..64]);
    if !is_valid_affine_point(&p_x, &p_y) {
        panic!("invalid input point")
    }
    let p_z = fe25519::one();
    let p = (p_x, p_y, p_z);
    let ptable = precompute_table(&p);
    let (windows, zeroth_window) = compute_windows(key);
    let mut x_q = fe25519::zero();
    let mut y_q = fe25519::zero();
    let mut z_q = fe25519::zero();
    y_q = y_q.cmov(&fe25519::one(), zeroth_window == 0);
    x_q = x_q.cmov(&p_x, zeroth_window == 1);
    y_q = y_q.cmov(&p_y, zeroth_window == 1);
    z_q = z_q.cmov(&p_z, zeroth_window == 1);
    let (x_q, y_q, z_q) = ladder((x_q, y_q, z_q), &windows, &ptable);
    let z_inverted = z_q.invert();
    let mut x_result = x_q.mul(&z_inverted);
    let mut y_result = y_q.mul(&z_inverted);

    let mut result = [0; 64];
    &mut result[0..32].copy_from_slice(&fe25519::pack(&mut x_result));
    &mut result[32..64].copy_from_slice(&fe25519::pack(&mut y_result));
    result
}

#[inline(never)]
fn benchmark(peripherals: &mut Peripherals) {
    let p = [
        0xDD, 0x50, 0xBE, 0xCC, 0xCD, 0xD3, 0x7D, 0x2B, 0x31, 0x72, 0xE0, 0x79, 0x1E, 0xDF, 0xD5,
        0x67, 0xE6, 0x4D, 0x14, 0xAA, 0xEA, 0xAC, 0x03, 0xDF, 0xDF, 0xA9, 0xDF, 0x3F, 0x22, 0x38,
        0x85, 0x70, 0x09, 0x0B, 0xE4, 0xA5, 0xED, 0xDE, 0xBF, 0xB6, 0x0F, 0x7B, 0x32, 0x25, 0x11,
        0x9D, 0x1C, 0x57, 0xDC, 0x78, 0x0F, 0x44, 0x57, 0x80, 0xB4, 0x43, 0x36, 0xD2, 0x1B, 0xAB,
        0x5E, 0x39, 0x49, 0x35,
    ];
    let key = [
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00,
    ];
    peripherals.DWT.enable_cycle_counter();

    // Measure baseline latency
    let tick = cortex_m::peripheral::DWT::get_cycle_count();
    let tock = cortex_m::peripheral::DWT::get_cycle_count();
    hprintln!("`blank(&p, &key)`").unwrap();
    hprintln!("  tock - tick: {} - {} = {}", tock, tick, tock - tick).unwrap();
    hprintln!().unwrap();
    let baseline = tock - tick;

    // Measure the latency of scalarmult function
    let tick = cortex_m::peripheral::DWT::get_cycle_count();
    let q = scalarmult(&p, &key);
    let tock = cortex_m::peripheral::DWT::get_cycle_count();
    hprintln!("`scalarmult(&p, &key)`").unwrap();
    hprintln!("  tock - tick: {} - {} = {}", tock, tick, tock - tick).unwrap();
    hprintln!().unwrap();
    let expected = [0; 64];
    assert_eq!(&q[..], &expected[..]);

    // Report
    let sample = tock - tick;
    let latency = sample - baseline;
    hprintln!(
        "Measured latency: {}cc (i.e. {}kcc)",
        latency,
        latency / 1000
    )
    .unwrap();
}

#[inline(never)]
fn micro_benchmark(_peripherals: &mut Peripherals) {
    /// Tell the compiler not to screw us over with their const-eval optimizations
    #[inline(always)]
    fn clobber() {
        unsafe{asm!(""::: "memory");}
    }
    
    // Micro-benchmark of add
    let tmp = fe25519::zero();
    let tick = cortex_m::peripheral::DWT::get_cycle_count();
    clobber();
    let tmp2 = fe25519::add(&tmp, &tmp);
    clobber();
    let tock = cortex_m::peripheral::DWT::get_cycle_count();
    hprintln!("`add(&tmp, &tmp)`").unwrap();
    hprintln!("  tock - tick: {} - {} = {}", tock, tick, tock - tick).unwrap();
    hprintln!().unwrap();
    unsafe {
        assert_eq!(&tmp2.as_uint8_t[..], &tmp.as_uint8_t[..]);
    }
    
    // Micro-benchmark of sub
    let tmp = fe25519::zero();
    let tick = cortex_m::peripheral::DWT::get_cycle_count();
    clobber();
    let tmp2 = fe25519::sub(&tmp, &tmp);
    clobber();
    let tock = cortex_m::peripheral::DWT::get_cycle_count();
    hprintln!("`sub(&tmp, &tmp)`").unwrap();
    hprintln!("  tock - tick: {} - {} = {}", tock, tick, tock - tick).unwrap();
    hprintln!().unwrap();
    unsafe {
        let expected = [237, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 127];
        assert_eq!(&tmp2.as_uint8_t[..], &expected[..]);
    }
    
    // Micro-benchmark of mul_u16
    let tmp = fe25519::zero();
    let tmp2 = tmp.clone();
    let tick = cortex_m::peripheral::DWT::get_cycle_count();
    clobber();
    let tmp2 = fe25519::mul_u16(tmp2, B);
    clobber();
    let tock = cortex_m::peripheral::DWT::get_cycle_count();
    hprintln!("`mul_u16(&tmp, B)`").unwrap();
    hprintln!("  tock - tick: {} - {} = {}", tock, tick, tock - tick).unwrap();
    hprintln!().unwrap();
    unsafe {
        assert_eq!(&tmp2.as_uint8_t[..], &tmp.as_uint8_t[..]);
    }
    
    // Micro-benchmark of mul
    let tmp = fe25519::zero();
    let tick = cortex_m::peripheral::DWT::get_cycle_count();
    clobber();
    let tmp2 = fe25519::mul(&tmp, &tmp);
    clobber();
    let tock = cortex_m::peripheral::DWT::get_cycle_count();
    hprintln!("`mul(&tmp, &tmp)`").unwrap();
    hprintln!("  tock - tick: {} - {} = {}", tock, tick, tock - tick).unwrap();
    hprintln!().unwrap();
    unsafe {
        assert_eq!(&tmp2.as_uint8_t[..], &tmp.as_uint8_t[..]);
    }

    // Micro-benchmark of square
    let tmp = fe25519::zero();
    let tick = cortex_m::peripheral::DWT::get_cycle_count();
    clobber();
    let tmp2 = fe25519::square(&tmp);
    clobber();
    let tock = cortex_m::peripheral::DWT::get_cycle_count();
    hprintln!("`square(&tmp, &tmp)`").unwrap();
    hprintln!("  tock - tick: {} - {} = {}", tock, tick, tock - tick).unwrap();
    hprintln!().unwrap();
    unsafe {
        assert_eq!(&tmp2.as_uint8_t[..], &tmp.as_uint8_t[..]);
    }
    
    // Micro-benchmark of select
    let table = [GE::default(); 16];
    let tick = cortex_m::peripheral::DWT::get_cycle_count();
    clobber();
    let tmp = select(0, &table);
    clobber();
    let tock = cortex_m::peripheral::DWT::get_cycle_count();
    hprintln!("`select(0, &table)`").unwrap();
    hprintln!("  tock - tick: {} - {} = {}", tock, tick, tock - tick).unwrap();
    hprintln!().unwrap();
    unsafe {
        assert_eq!(&tmp.0.as_uint8_t[..], &table[0].0.as_uint8_t[..]);
    }
    
    // Micro-benchmark of double
    let p = GE::default();
    let tick = cortex_m::peripheral::DWT::get_cycle_count();
    clobber();
    let tmp = ge_double(&p);
    clobber();
    let tock = cortex_m::peripheral::DWT::get_cycle_count();
    hprintln!("`double(&p)`").unwrap();
    hprintln!("  tock - tick: {} - {} = {}", tock, tick, tock - tick).unwrap();
    hprintln!().unwrap();
    unsafe {
        // assert_eq!(&tmp.0.as_uint8_t[..], &p.0.as_uint8_t[..]);
    }
    
    // Micro-benchmark of add
    let p = GE::default();
    let tick = cortex_m::peripheral::DWT::get_cycle_count();
    clobber();
    let tmp = ge_add(&p, &p);
    clobber();
    let tock = cortex_m::peripheral::DWT::get_cycle_count();
    hprintln!("`add(&p, &p)`").unwrap();
    hprintln!("  tock - tick: {} - {} = {}", tock, tick, tock - tick).unwrap();
    hprintln!().unwrap();
    unsafe {
        // assert_eq!(&tmp.0.as_uint8_t[..], &p.0.as_uint8_t[..]);
    }
    
    // Micro-benchmark of invert
    let tmp = fe25519::zero();
    let tick = cortex_m::peripheral::DWT::get_cycle_count();
    clobber();
    let tmp2 = fe25519::invert(&tmp);
    clobber();
    let tock = cortex_m::peripheral::DWT::get_cycle_count();
    hprintln!("`invert(&tmp, &tmp)`").unwrap();
    hprintln!("  tock - tick: {} - {} = {}", tock, tick, tock - tick).unwrap();
    hprintln!().unwrap();
    unsafe {
        assert_eq!(&tmp2.as_uint8_t[..], &tmp.as_uint8_t[..]);
    }
}

#[entry]
/// Entrypoint of this program
fn main() -> ! {
    tests::do_tests();

    let mut peripherals = Peripherals::take().unwrap();

    // Do micro-benchmarks
    micro_benchmark(&mut peripherals);

    // Macro-benchmark scalar multiplication
    benchmark(&mut peripherals);

    cortex_m::asm::bkpt();
    loop {}
}

mod tests {
    use super::*;

    pub fn do_tests() {
        test_neutral();
        test_identity();
        test_random_point();
    }

    fn test_neutral() {
        hprint!("test_neutral... ").unwrap();
        let p = [
            0xDD, 0x50, 0xBE, 0xCC, 0xCD, 0xD3, 0x7D, 0x2B, 0x31, 0x72, 0xE0, 0x79, 0x1E, 0xDF,
            0xD5, 0x67, 0xE6, 0x4D, 0x14, 0xAA, 0xEA, 0xAC, 0x03, 0xDF, 0xDF, 0xA9, 0xDF, 0x3F,
            0x22, 0x38, 0x85, 0x70, 0x09, 0x0B, 0xE4, 0xA5, 0xED, 0xDE, 0xBF, 0xB6, 0x0F, 0x7B,
            0x32, 0x25, 0x11, 0x9D, 0x1C, 0x57, 0xDC, 0x78, 0x0F, 0x44, 0x57, 0x80, 0xB4, 0x43,
            0x36, 0xD2, 0x1B, 0xAB, 0x5E, 0x39, 0x49, 0x35,
        ];
        let key = [
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
        ];
        let expected = [0; 64];
        let q = scalarmult(&p, &key);
        assert_eq!(&q[..], &expected[..]);
        hprint!("ok\n").unwrap();
    }

    fn test_identity() {
        hprint!("test_identity... ").unwrap();
        let p = [
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0xb3, 0x2b, 0x6a, 0xf7, 0xce, 0xb0, 0xc9, 0x4d, 0x89, 0xe0,
            0x7a, 0xb0, 0x4c, 0x5d, 0x1d, 0x45, 0xbe, 0x89, 0x11, 0x67, 0x69, 0xac, 0xec, 0xac,
            0xe1, 0x48, 0xf3, 0x7, 0x5e, 0x80, 0xf0, 0x11,
        ];
        let key = [
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
        ];
        let expected = p;
        let q = scalarmult(&p, &key);
        assert_eq!(&q[..], &expected[..]);
        hprint!("ok\n").unwrap();
    }

    fn test_random_point() {
        hprint!("test_random_point... ").unwrap();
        let p = [
            0xDD, 0x50, 0xBE, 0xCC, 0xCD, 0xD3, 0x7D, 0x2B, 0x31, 0x72, 0xE0, 0x79, 0x1E, 0xDF,
            0xD5, 0x67, 0xE6, 0x4D, 0x14, 0xAA, 0xEA, 0xAC, 0x03, 0xDF, 0xDF, 0xA9, 0xDF, 0x3F,
            0x22, 0x38, 0x85, 0x70, 0x09, 0x0B, 0xE4, 0xA5, 0xED, 0xDE, 0xBF, 0xB6, 0x0F, 0x7B,
            0x32, 0x25, 0x11, 0x9D, 0x1C, 0x57, 0xDC, 0x78, 0x0F, 0x44, 0x57, 0x80, 0xB4, 0x43,
            0x36, 0xD2, 0x1B, 0xAB, 0x5E, 0x39, 0x49, 0x35,
        ];
        let expected = [
            0x0B, 0xCC, 0x06, 0xFC, 0x25, 0x72, 0x9D, 0x74, 0x6C, 0xB5, 0xB1, 0xCB, 0xA4, 0xEE,
            0x41, 0x3C, 0xFA, 0xD7, 0xA2, 0x72, 0xF5, 0x3A, 0x8A, 0x91, 0x3C, 0x04, 0x9E, 0x2D,
            0x9A, 0x11, 0xEC, 0x20, 0x2D, 0xEF, 0xCC, 0x0B, 0x92, 0xB9, 0x0D, 0xF8, 0x67, 0xE5,
            0x67, 0xEB, 0x3B, 0x5F, 0x87, 0x81, 0x2D, 0x96, 0xEC, 0x00, 0x53, 0x8D, 0x5B, 0xDD,
            0xE2, 0xE6, 0xD5, 0x19, 0x20, 0x3A, 0xEE, 0x59,
        ];

        let key = [
            0x2A, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
        ];
        let q = scalarmult(&p, &key);
        assert_eq!(&q[..], &expected[..]);
        hprint!("ok\n").unwrap();
    }
}
