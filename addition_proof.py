from pypcs.curve import Fp, Fr, ec_mul, G1Point
import random

# Zero-Knowledge Addition Proof


# TODO: should move to common file
class PedersenParams:
    def __init__(self):
        self.G = G1Point.ec_gen_group1()
        self.H = self.generateH()

    @staticmethod
    def generateH() -> G1Point:
        # generate a random point as H
        r = Fr.rand(random.Random("hash-to-point"))
        return ec_mul(G1Point.ec_gen_group1(), r)


def commit(sk: Fr, rho: Fr, pp: PedersenParams) -> G1Point:
    """
    Computationally hiding
    Statistically binding
    """
    return ec_mul(G1Point.ec_gen_group1(), sk) + ec_mul(pp.H, rho)


class Prover:
    a: Fr
    b: Fr
    c: Fr  # c = a + b
    tau_a: Fr
    tau_b: Fr
    tau_c: Fr

    A: G1Point
    B: G1Point
    C: G1Point  # C = [c;tau_c]

    r_a: Fr
    r_b: Fr
    r_c: Fr  # r_c = r_a + r_b
    rho_a: Fr
    rho_b: Fr
    rho_c: Fr

    pp: PedersenParams
    rnd_gen: random.Random

    def __init__(self, a: Fr, b: Fr, pp: PedersenParams):
        self.rnd_gen = random.Random("addition-prover")

        self.a = a
        self.b = b
        self.c = a + b

        self.tau_a = Fr.rand(self.rnd_gen)
        self.tau_b = Fr.rand(self.rnd_gen)
        self.tau_c = Fr.rand(self.rnd_gen)
        self.pp = pp

        self.A = commit(self.a, self.tau_a, self.pp)
        self.B = commit(self.b, self.tau_b, self.pp)
        self.C = commit(self.c, self.tau_c, self.pp)

    def round1(self) -> tuple[G1Point, G1Point, G1Point]:
        self.r_a = Fr.rand(self.rnd_gen)
        self.r_b = Fr.rand(self.rnd_gen)
        self.r_c = self.r_a + self.r_b

        self.rho_a = Fr.rand(self.rnd_gen)
        self.rho_b = Fr.rand(self.rnd_gen)
        self.rho_c = Fr.rand(self.rnd_gen)

        R_A = commit(self.r_a, self.rho_a, self.pp)
        R_B = commit(self.r_b, self.rho_b, self.pp)
        R_C = commit(self.r_c, self.rho_c, self.pp)

        return R_A, R_B, R_C

    def round3(self, e: Fr) -> tuple[Fr, Fr, Fr, Fr, Fr]:
        z_a = self.r_a + e * self.a
        z_tau_a = self.rho_a + e * self.tau_a

        z_b = self.r_b + e * self.b
        z_tau_b = self.rho_b + e * self.tau_b

        z_tau_c = self.rho_c + e * self.tau_c

        return z_a, z_b, z_tau_a, z_tau_b, z_tau_c


class Verifier:
    A: G1Point
    B: G1Point
    C: G1Point

    pp: PedersenParams
    rnd_gen: random.Random

    def __init__(self, A: G1Point, B: G1Point, C: G1Point, pp: PedersenParams):
        self.rnd_gen = random.Random("addition-verifier")

        self.A = A
        self.B = B
        self.C = C

        self.pp = pp

    def round2(self: G1Point) -> Fr:
        e = Fr.rand(self.rnd_gen)
        return e

    def verify(
        self,
        e: Fr,
        R_A: G1Point,
        R_B: G1Point,
        R_C: G1Point,
        z_a: Fr,
        z_b: Fr,
        z_tau_a: Fr,
        z_tau_b: Fr,
        z_tau_c: Fr,
    ) -> bool:
        """
        [z_a;z_tau_a] ?= R_A + A * e
        [z_b;z_tau_b] ?= R_B + B * e
        [z_a+z_b;z_tau_c] ?= R_C + C * e
        """
        return (
            commit(z_a, z_tau_a, self.pp) == R_A + ec_mul(self.A, e)
            and commit(z_b, z_tau_b, self.pp) == R_B + ec_mul(self.B, e)
            and commit((z_a + z_b), z_tau_c, self.pp) == R_C + ec_mul(self.C, e)
        )


def run_addition_proof(a: Fr, b: Fr, pp: PedersenParams) -> bool:
    prover = Prover(a, b, pp)
    verifier = Verifier(prover.A, prover.B, prover.C, pp)

    R_A, R_B, R_C = prover.round1()
    e = verifier.round2()
    z_a, z_b, z_tau_a, z_tau_b, z_tau_c = prover.round3(e)
    return verifier.verify(e, R_A, R_B, R_C, z_a, z_b, z_tau_a, z_tau_b, z_tau_c)


if __name__ == "__main__":
    pedersen_params = PedersenParams()
    a = Fr(31)
    b = Fr(19)
    print(f"?: {run_addition_proof(a, b, pedersen_params)}")
    # print(
    #     f"?: {simulate(commit(sk, rho, pedersen_params), Verifier(commit(sk, rho, pedersen_params), pedersen_params))}"
    # )
    # print(f"?: {extract(Prover(sk, rho))}")
