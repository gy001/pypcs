from pypcs.curve import Fp, Fr, ec_mul, G1Point
import random


def generateG1() -> G1Point:
    # generate a random point as H
    r = Fr.rand(random.Random("hash-to-point"))
    return ec_mul(G1Point.ec_gen_group1(), r)


G_0 = G1Point.ec_gen_group1()
G_1 = generateG1()


def commit(a_0: Fr, a_1: Fr) -> G1Point:
    """
    Computationally hiding
    Statistically binding
    """
    return ec_mul(G_0, a_0) + ec_mul(G_1, a_1)


class Prover:
    a_0: Fr
    a_1: Fr
    r_0: Fr
    r_1: Fr
    z_0: Fr
    z_1: Fr
    A: G1Point

    def __init__(self, a_0: Fr, a_1: Fr):
        self.a_0 = a_0
        self.a_1 = a_1
        self.A = commit(a_0, a_1)
        self.rnd_gen = random.Random("split_and_fold_prover")

    def round1(self) -> G1Point:
        self.r_0 = Fr.rand(self.rnd_gen)
        self.r_1 = Fr.rand(self.rnd_gen)
        R = commit(self.r_0, self.r_1)
        return R

    def round3(self, c: Fr) -> tuple[G1Point, G1Point]:
        self.z_0 = self.r_0 + c * self.a_0
        self.z_1 = self.r_1 + c * self.a_1
        return ec_mul(G_0, self.z_1), ec_mul(G_1, self.z_0)

    def round5(self, mu: Fr) -> Fr:
        return self.z_0 + mu * self.z_1


class Verifier:
    A: G1Point
    rnd_gen: random.Random

    def __init__(self, A: G1Point):
        self.A = A
        self.rnd_gen = random.Random("split_and_fold_verifier")

    def round2(self) -> Fr:
        c = Fr.rand(self.rnd_gen)
        return c

    def round4(self) -> Fr:
        mu = Fr.rand(self.rnd_gen)
        return mu

    def verify(
        self, R: G1Point, c: Fr, Z_L: G1Point, Z_R: G1Point, mu: Fr, z: Fr
    ) -> bool:
        """
        [z] ?= [r] + c * sk
        """
        return ec_mul(G_0 + ec_mul(G_1, 1 / mu), z) == R + ec_mul(self.A, c) + ec_mul(
            Z_L, mu
        ) + ec_mul(Z_R, 1 / mu)


def run_split_and_fold(a_0: Fr, a_1: Fr) -> bool:
    prover = Prover(a_0, a_1)
    verifier = Verifier(prover.A)

    R = prover.round1()
    c = verifier.round2()
    Z_L, Z_R = prover.round3(c)
    mu = verifier.round4()
    z = prover.round5(mu)
    return verifier.verify(R, c, Z_L, Z_R, mu, z)


if __name__ == "__main__":
    a_0 = Fr(31)
    a_1 = Fr(17)
    print(f"A: {commit(a_0, a_1)}")
    print(f"?: {run_split_and_fold(a_0, a_1)}")
