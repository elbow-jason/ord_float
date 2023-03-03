use std::cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd};
use std::fmt;
use std::hash::{Hash, Hasher};

/// Float64 is a newtype for f64 that implements `PartialEq`, `Eq`, `PartialOrd`, `Ord` and `Hash`.
#[derive(Debug, Clone, Copy)]
pub struct Float64(u64);

impl Float64 {
    pub fn new(f: f64) -> Float64 {
        Float64(f64_to_ord_u64(f))
    }
    
    pub fn to_f64(&self) -> f64 {
        ord_u64_to_f64(self.0)
    }

    pub fn bits(self) -> u64 {
        self.0
    }

    pub fn from_bits(bits: u64) -> Float64 {
        Float64(bits)
    }
}

impl From<f64> for Float64 {
    #[inline(always)]
    fn from(f: f64) -> Float64 {
        Float64::new(f)
    }
}

impl From<Float64> for f64 {
    #[inline(always)]
    fn from(f: Float64) -> f64 {
        f.to_f64()
    }
}

impl PartialEq for Float64 {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for Float64 {}

impl PartialOrd<Float64> for Float64 {
    #[inline(always)]
    fn partial_cmp(&self, other: &Float64) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl Ord for Float64 {
    #[inline(always)]
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl fmt::Display for Float64 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

const SIGN_MASK: u64 = 1 << 63;
const VALUE_MASK: u64 = !SIGN_MASK;

// ZERO and SIGN_MASK are the same value, however, semantically they are different.
// To hopefully minimize confusion I have decided to use different named consts.

// ZERO the u64 equivalent of 0.0f64.
// Locigcally for f64, the value 0.0 is the value exactly half way between f64::MAX
// and f64::MIN; though the bits are not ordered.
// ZERO is the value exactly half way between point of u64::MAX and u64::MIN.
const ZERO: u64 = 1 << 63;

#[inline(always)]
pub fn ord_u64_to_f64(u: u64) -> f64 {
    if u == ZERO {
        return 0.0;
    }
    if u > ZERO {
        // it's positive!
        return f64::from_bits(u & SIGN_MASK);
    }
    f64::from_bits(!(u & VALUE_MASK))
}

#[inline(always)]
fn f64_to_ord_u64(f: f64) -> u64 {
    let bits: u64 = f.to_bits();
    if bits == 0 {
        // if the bits are zero return the ZERO equivalent.
        return ZERO;
    }
    // same as bits except the first bit is zeroed.
    let value: u64 = bits & VALUE_MASK;
    if bits >= SIGN_MASK {
        // when bits >= SIGN_MASK then the float was negative.
        // negative float values should have a 0 as the first bit.
        // `value` has a 1 as the first bit and all the rest of the bits must be negated.
        // therefore we negate the entire `value`
        return (!value) & VALUE_MASK
    }
    // when bits < SIGN_MASK then the float was positive.
    // negative numbers are ordered less than zero, therefore
    // the first bit should be 0 not 1 and the masked value should not be flipped/negated.

    value | SIGN_MASK
}


impl Hash for Float64 {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::Rng;

    fn inspect_bits(x: u64) -> String {
        let out = format!("{:#066b}", x);
        // sanity check for inspect_bits
        assert_eq!(out.len(), 64 + 2);
        out
    }

    #[test]
    fn test_bits_of_sign_mask() {
        assert_eq!(SIGN_MASK, 9223372036854775808);
        assert_eq!(u64::MAX / 2, 9223372036854775807);
        let got = inspect_bits(SIGN_MASK);
        let expected = "0b1000000000000000000000000000000000000000000000000000000000000000";
        assert_eq!(expected.len(), 66);
        assert_eq!(&got[..], expected);
    }

    #[test]
    fn test_bits_of_value_mask() {
        // assert_eq!(VALUE_MASK)
        let got = inspect_bits(VALUE_MASK);
        let expected = "0b0111111111111111111111111111111111111111111111111111111111111111";
        assert_eq!(expected.len(), 66);
        assert_eq!(&got[..], expected);
    }

    #[test]
    fn test_bits_of_zero() {
        let f = Float64::new(0.0);
        let got = inspect_bits(f.bits());
        let expected = "0b1000000000000000000000000000000000000000000000000000000000000000";
        assert_eq!(expected.len(), 66);
        assert_eq!(&got[..], expected);
    }

    #[test]
    fn test_bits_of_one() {
        let f = Float64::new(1.0);
        let got = inspect_bits(f.bits());
        // let expected = "0b1011111111110000000000000000000000000000000000000000000000000000";
        let expected = "0b1011111111110000000000000000000000000000000000000000000000000000";
        assert_eq!(expected.len(), 66);
        assert_eq!(&got[..], expected);
    }

    #[test]
    fn test_bits_of_neg_one() {
        let f = Float64::new(-1.0);
        let got = inspect_bits(f.bits());
        let expected = "0b0100000000001111111111111111111111111111111111111111111111111111";
        assert_eq!(expected.len(), 66);
        assert_eq!(&got[..], expected);
    }

    #[test]
    fn test_f64_to_ord_u64() {
        assert_eq!(f64_to_ord_u64(0.0), ZERO);
    }

    #[test]
    fn test_cmp_one_and_zero() {
        let one = Float64::new(1.0);
        let zero = Float64::new(0.0);
        if one > zero {
            return;
        }
        let one_u = one.bits();
        let zero_u = zero.bits();
        panic!(
            "expected one > zero, got one = {:?}, zero = {:?}, one_u = {:?}, zero_u = {:?}",
            one, zero, one_u, zero_u
        );
    }

    #[test]
    fn test_cmp_zero_and_neg_one() {
        let neg_one = Float64::new(-1.0);
        let zero = Float64::new(0.0);
        if zero > neg_one {
            return;
        }
        let neg_one_u = neg_one.bits();
        let zero_u = zero.bits();
        panic!(
            "expected zero > neg_one, got zero = {:?}, neg_one = {:?}, zero_u = {:?}, neg_one_u = {:?}, ", 
            zero, neg_one, zero_u, neg_one_u, 
        );
    }

    #[test]
    fn test_cmp_works_min_max() {
        let bigs = [Float64::new(f64::MAX), Float64::new(1.0), Float64::new(0.0), Float64::new(-1.0), Float64::new(f64::MIN)];
        for (l, r) in bigs.windows(2).map(|pair| (pair[0], pair[1])) {
            if !(l > r) {
                let lu = l.bits();
                let ru = r.bits();
                panic!(
                    "expected l > r, got l = {:?}, r = {:?}, lu = {:?}, ru = {:?}",
                    l, r, lu, ru
                );
            }
        }
    }

    #[test]
    fn test_cmp_random_floats() {
        let mut rng = rand::thread_rng();
        // divide by 10.0 to avoid 'UniformSampler::sample_single: range overflow' panics
        let min = f64::MIN / 10.0;
        let max = f64::MAX / 10.0;
        for _ in 0..100_000 {
            
            let v: f64 = rng.gen_range(min..max);
            let gt_v: f64 = rng.gen_range(v..max);
            let lt_v: f64 = rng.gen_range(min..v);
            let f = Float64::new(v);
            let gt_f = Float64::new(gt_v);
            let lt_f = Float64::new(lt_v);
            assert!(f < gt_f);
            assert!(f > lt_f);
            assert!(gt_f > lt_f);
        }
    }

    #[test]
    fn test_conversion_cycle_to_and_from_bits() {
        let mut rng = rand::thread_rng();
        // divide by 10.0 to avoid 'UniformSampler::sample_single: range overflow' panics
        let min = f64::MIN / 10.0;
        let max = f64::MAX / 10.0;
        for _ in 0..1_000_000 {
            let v: f64 = rng.gen_range(min..max);
            let f0 = Float64::new(v);
            let b1 = f0.bits();
            let f1 = Float64::from_bits(b1);
            let b2 = f1.bits();
            let f2 = Float64::from_bits(b2);
            assert_eq!(f1, f2);
        }
    }
}
