use std::iter;

/// Integer representation of primitive polynomial in GF(2).
const PRIMITIVES: [usize; 32] = [
    1,          // [0]
    3,          // [0, 1]
    7,          // [0, 1, 2]
    11,         // [0, 1, 3]
    19,         // [0, 1, 4]
    37,         // [0, 2, 5]
    67,         // [0, 1, 6]
    131,        // [0, 1, 7]
    285,        // [0, 2, 3, 4, 8]
    529,        // [0, 4, 9]
    1033,       // [0, 3, 10]
    2053,       // [0, 2, 11]
    4179,       // [0, 1, 4, 6, 12]
    8219,       // [0, 1, 3, 4, 13]
    16427,      // [0, 1, 3, 5, 14]
    32771,      // [0, 1, 15]
    65581,      // [0, 2, 3, 5, 16]
    131081,     // [0, 3, 17]
    262183,     // [0, 1, 2, 5, 18]
    524327,     // [0, 1, 2, 5, 19]
    1048585,    // [0, 3, 20]
    2097157,    // [0, 2, 21]
    4194307,    // [0, 1, 22]
    8388641,    // [0, 5, 23]
    16777243,   // [0, 1, 3, 4, 24]
    33554441,   // [0, 3, 25]
    67108935,   // [0, 1, 2, 6, 26]
    134217767,  // [0, 1, 2, 5, 27]
    268435465,  // [0, 3, 28]
    536870917,  // [0, 2, 29]
    1073741907, // [0, 1, 4, 6, 30]
    2147483657, // [0, 3, 31]
];

/// Integer representation of 1/X in GF(2).
const X_INVS: [usize; 32] = [
    0,          // []
    1,          // [0]
    3,          // [0, 1]
    5,          // [0, 2]
    9,          // [0, 3]
    18,         // [1, 4]
    33,         // [0, 5]
    65,         // [0, 6]
    142,        // [1, 2, 3, 7]
    264,        // [3, 8]
    516,        // [2, 9]
    1026,       // [1, 10]
    2089,       // [0, 3, 5, 11]
    4109,       // [0, 2, 3, 12]
    8213,       // [0, 2, 4, 13]
    16385,      // [0, 14]
    32790,      // [1, 2, 4, 15]
    65540,      // [2, 16]
    131091,     // [0, 1, 4, 17]
    262163,     // [0, 1, 4, 18]
    524292,     // [2, 19]
    1048578,    // [1, 20]
    2097153,    // [0, 21]
    4194320,    // [4, 22]
    8388621,    // [0, 2, 3, 23]
    16777220,   // [2, 24]
    33554467,   // [0, 1, 5, 25]
    67108883,   // [0, 1, 4, 26]
    134217732,  // [2, 27]
    268435458,  // [1, 28]
    536870953,  // [0, 3, 5, 29]
    1073741828, // [2, 30]
];

#[derive(Debug, Clone, Copy)]
pub struct BooleanHypercube {
    num_vars: usize,
    primitive: usize,
    x_inv: usize,
}

impl BooleanHypercube {
    pub fn new(num_vars: usize) -> Self {
        assert!(num_vars <= 31);
        Self {
            num_vars,
            primitive: PRIMITIVES[num_vars],
            x_inv: X_INVS[num_vars],
        }
    }

    pub fn primitive(&self) -> usize {
        self.primitive
    }

    pub fn x_inv(&self) -> usize {
        self.x_inv
    }

    pub fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        let mut b = 1;
        iter::once(0)
            .chain(iter::repeat_with(move || {
                let item = b;
                b = next(b, self.num_vars, self.primitive);
                item
            }))
            .take(1 << self.num_vars)
    }

    pub fn next_map(&self) -> Vec<usize> {
        (0..1 << self.num_vars)
            .map(|b| next(b, self.num_vars, self.primitive))
            .collect()
    }

    pub fn prev_map(&self) -> Vec<usize> {
        (0..1 << self.num_vars)
            .map(|b| prev(b, self.primitive))
            .collect()
    }

    pub fn idx_map(&self) -> Vec<usize> {
        let mut idx_map = vec![0; 1 << self.num_vars];
        let mut b = 1;
        for idx in 1..1 << self.num_vars {
            idx_map[b] = idx;
            b = next(b, self.num_vars, self.primitive);
        }
        idx_map
    }
}

#[inline(always)]
fn next(mut b: usize, num_vars: usize, primitive: usize) -> usize {
    b <<= 1;
    b ^= (b >> num_vars) * primitive;
    b
}

#[inline(always)]
fn prev(b: usize, x_inv: usize) -> usize {
    (b >> 1) ^ ((b & 1) * x_inv)
}

#[cfg(test)]
mod test {
    use crate::util::arithmetic::BooleanHypercube;

    #[test]
    #[ignore = "Cause it takes some minutes to run with release profile"]
    fn test_boolean_hypercube() {
        for num_vars in 0..32 {
            let bh = BooleanHypercube::new(num_vars);
            let mut set = vec![false; 1 << num_vars];
            for i in bh.iter() {
                if set[i] {
                    panic!(
                        "Found repeated item while iterating the boolean hypercube with {num_vars}"
                    );
                }
                set[i] = true;
            }
        }
    }
}
