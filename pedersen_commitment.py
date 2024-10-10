from pypcs.curve import Fp, Fr, ec_mul, G1Point
import random

# (HV) Computational Zero-Knowledge pedersen Protocol


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
    sk: Fr
    rho: Fr
    r: Fr
    r_rho: Fr
    pk: G1Point
    pp: PedersenParams
    rnd_gen: random.Random

    def __init__(self, sk: Fr, rho: Fr):
        self.sk = sk
        self.rho = rho
        self.pp = PedersenParams()
        self.pk = commit(sk, rho, self.pp)
        self.rnd_gen = random.Random("pedersen-prover")

    def round1(self) -> G1Point:
        self.r = Fr.rand(self.rnd_gen)
        self.r_rho = Fr.rand(self.rnd_gen)
        R = commit(self.r, self.r_rho, self.pp)
        return R

    def round3(self, c: Fr) -> tuple[Fr, Fr]:
        z = self.r + c * self.sk
        z_rho = self.r_rho + c * self.rho
        return z, z_rho


class Verifier:
    pk: G1Point
    pp: PedersenParams
    rnd_gen: random.Random

    def __init__(self, pk: G1Point, pp: PedersenParams):
        self.pk = pk
        self.pp = pp
        self.rnd_gen = random.Random("pederson-verifier")

    def round2(self: G1Point) -> Fr:
        c = Fr.rand(self.rnd_gen)
        return c

    def verify(self, R: G1Point, c: Fr, z: Fr, z_rho: Fr) -> bool:
        """
        [z;z_rho] ?= [r;r_rho] + c * pk
        """
        return commit(z, z_rho, self.pp) == R + ec_mul(self.pk, c)


def run_pedersen(sk: Fr, rho: Fr, pp: PedersenParams) -> bool:
    prover = Prover(sk, rho)
    verifier = Verifier(prover.pk, pp)

    R = prover.round1()
    c = verifier.round2()
    z, z_rho = prover.round3(c)
    return verifier.verify(R, c, z, z_rho)


def simulate(prover_pk: G1Point, verifier: Verifier) -> Fr:
    pp = verifier.pp

    # 1 simulator does Round 1 of prover
    r = Fr(1)
    r_rho = Fr(1)
    R = commit(r, r_rho, pp)

    # 2. simulator invoke Round 2 of verifier
    st = verifier.rnd_gen.getstate()
    c = verifier.round2()

    # 3. simulator does Round 3 of prover
    z_star = Fr.rand(random.Random("pedersen-sim-z"))
    z_rho_star = Fr.rand(random.Random("pedersen-sim-z-rho"))
    Z_star = commit(z_star, z_rho_star, pp)

    R_star = Z_star - ec_mul(prover_pk, c)
    verifier.rnd_gen.setstate(st)
    c_star = verifier.round2()

    assert c == c_star

    return verifier.verify(R_star, c, z_star, z_rho_star)


def extract(prover: Prover) -> tuple[Fr, Fr]:
    rng = random.Random("pedersen-extract")

    R = prover.round1()
    
    c_1 = Fr.rand(rng)
    c_2 = Fr.rand(rng)
    
    z_1, z_rho_1 = prover.round3(c_1)
    z_2, z_rho_2 = prover.round3(c_2)
    sk = (z_2 - z_1) / (c_2 - c_1)
    rho = (z_rho_2 - z_rho_1) / (c_2 - c_1)
    
    return sk, rho


if __name__ == "__main__":
    pedersen_params = PedersenParams()
    sk = Fr(31)
    rho = Fr(19)
    print(f"sk: {sk};{rho}")
    print(f"pk: {commit(sk, rho, pedersen_params)}")
    print(f"?: {run_pedersen(sk, rho, pedersen_params)}")
    print(
        f"?: {simulate(commit(sk, rho, pedersen_params), Verifier(commit(sk, rho, pedersen_params), pedersen_params))}"
    )
    print(f"?: {extract(Prover(sk, rho))}")
