from typing import NewType, Generic, TypeVar
from random import randint, seed, Random
# from galois import GF

from py_ecc.fields.field_elements import FQ
import py_ecc.bn128 as bn128

primitive_root = 5

# G1Point = NewType("G1Point", tuple[b.FQ, b.FQ])
G2Point = NewType("G2Point", tuple[bn128.FQ2, bn128.FQ2])

BN128_CURVE_ORDER = bn128.curve_order

class Fr(FQ):
    field_modulus = bn128.curve_order

    @classmethod
    def rand(cls, rndg: Random) -> "Fr":
        return cls(rndg.randint(1, cls.field_modulus - 1))
    
    @classmethod
    def rands(cls, rndg: Random, n: int) -> list["Fr"]:
        return [cls(rndg.randint(1, cls.field_modulus - 1)) for _ in range(n)]

Fp = NewType("BaseField", bn128.FQ)

class G1Point:
    def __init__(self, x: Fp, y: Fp, is_zero: bool = False):
        self.x = x
        self.y = y
        self.is_zero = is_zero
    
    @classmethod
    def ec_gen_group1(cls) -> "G1Point":
        return cls(bn128.G1[0], bn128.G1[1])

    def __eq__(self, other: "G1Point") -> bool:
        if self.is_zero and other.is_zero:
            return True
        elif not self.is_zero and not other.is_zero:
            return self.x == other.x and self.y == other.y
        return False

    def __add__(self, other: "G1Point") -> "G1Point":
        if self.is_zero:
            return other
        if other.is_zero:
            return self
        result = bn128.add((self.x, self.y), (other.x, other.y))
        return G1Point(result[0], result[1])

    def __sub__(self, other: "G1Point") -> "G1Point":
        if self == G1Point.zero():
            return other
        if other == G1Point.zero():
            return self
        result = bn128.add((self.x, self.y), bn128.neg((other.x, other.y)))
        return G1Point(result[0], result[1])
    
    # def __mul__(self, other: Fr) -> "G1Point":
    #     return ec_mul(self, other)

    # def __rmul__(self, other: Fr) -> "G1Point":
    #     return ec_mul(self, other)

    def __str__(self) -> str:
        return f"({self.x}, {self.y})"
    
    def __repr__(self) -> str:
        return f"G1Point({self.x}, {self.y})"
    
    def __hash__(self) -> int:
        return hash((self.x, self.y))
    
    def zero() -> "G1Point":
        return G1Point(bn128.Z1, bn128.Z1, is_zero=True)

    # def ec_identity() -> G1Point:
    # return bn128.Z1

def ec_mul(pt: G1Point, coeff: Fr) -> G1Point:
    if pt.is_zero:
        return G1Point.zero()
    if coeff == Fr.zero():
        return G1Point.zero()
    h = bn128.multiply((pt.x, pt.y), coeff.n)
    return G1Point(h[0], h[1])

def ec_gen_group2() -> G2Point:
    return bn128.G2



def ec_id_group2() -> G2Point:
    return b.Z2

def ec_lincomb(pairs: list[tuple[G1Point, Fr]]) -> G1Point:
    o = bn128.Z1
    for pt, coeff in pairs:
        o = bn128.add(o, ec_mul(pt, coeff))
    return o

# def poly_test():

#     Fr = Scalar(BN128_CURVE_ORDER)

#     vals = [1, 2, 3, 4]
#     vals_scalar = [Scalar(int(x)) for x in vals]
#     roots_of_unity = Scalar.roots_of_unity(4)

#     poly_lag = Polynomial(vals_scalar, Basis.LAGRANGE)
#     poly_coeff = poly_lag.ifft()
#     points = roots_of_unity + [Scalar(2), Scalar(3), Scalar(4)]
#     for i in range(len(points)):
#       point = points[i]
#       eval_lag = poly_lag.barycentric_eval(point)
#       coeff_eval = poly_coeff.coeff_eval(point)
#       assert eval_lag == coeff_eval

#     quo = poly_coeff / Scalar(2)
#     print("quo: ", quo.values)


if __name__ == "__main__":
    print(f"type(b.G1): {type(bn128.G1)}")
    print(f"type(b.Z1): {type(bn128.Z1)}")
    print(f"b.curve_order: {bn128.curve_order}")
    print(f"Fr(3) + Fr(9): {Fr(3) + Fr(9)}")
    print(f"Fr(3) * Fr(4): {Fr(3) * Fr(4)}")
    print(f"Fr(3) - Fr(5): {Fr(3) - Fr(5)}")
    print(f"Fr(3) / Fr(5): {Fr(3) / Fr(5)}")
    print(f"Fr(3) ** 2: {Fr(3) ** 2}")

    a = Fr(8)
    g = G1Point.ec_gen_group1()
    print(f"g: {g}")
    print(f" > ec_mul(g, a): {ec_mul(g, a)}")
    # print(f" > ec_mul(g, a): {ec_add(ec_mul(g, Fr(3)), ec_mul(g, Fr(5))) }")
    print(f" > ec_mul(g, a): {ec_mul(g, Fr(3)) + ec_mul(g, Fr(5)) }")

    a = G1Point(bn128.G1[0], bn128.G1[1])
    b = a + a
    print(f"b: {b}")
    print(f"b.G1.double(): {bn128.double(bn128.G1)}")

