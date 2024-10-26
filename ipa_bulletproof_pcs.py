#!/usr/bin/env python3

# WARNING: This implementation may contain bugs and has not been audited. 
# It is only for educational purposes. DO NOT use it in production.

from pypcs.curve import Fp, Fr, ec_mul, G1Point
from merlin.merlin_transcript import MerlinTranscript

from pedersen import PedersenCommitment

# WARNING: 
#   1. For demonstration, we deliberately use an insecure random number 
#      generator, random.Random. To generate secure randomness, use 
#      the standard library `secrets` instead.
#        
#      See more here: https://docs.python.org/3/library/secrets.html
#
#   2. Challenges are only 1 byte long for simplicity, which is not secure.

import random

# Implementation of the BulletproofIPA PCS from the following paper:
#   Bulletproofs: https://eprint.iacr.org/2017/1066.pdf
#
# The implementation of ZK is slightly different from the original 
# paper. The original paper adds a Vector Schnorr protocol on the 
# outer layer, while this implementation uses the method from the 
# Hyrax paper, adding two blinders in each recursive round, 
# and then using a Schnorr protocol (in the inner layer) to open 
# in the final open phase.
#
#   Hyrax: https://eprint.iacr.org/2017/1132.pdf


# TODO:
# - add options for the blinders
# - add batch proving and verifying


IPA_Argument = tuple[int,G1Point, G1Point, G1Point, list[Fr]]

class IPA_PCS:

    pcs: PedersenCommitment

    def __init__(self, pcs: PedersenCommitment):
        """
        Args:
            pcs: the PedersenCommitment instance to use for the proof
        """
        self.pcs = pcs
        self.rnd_gen = random.Random("ipa-pcs")

    def commit(self, vec_c: list[Fr]) -> tuple[G1Point, Fr]:
        """
        Commit to a vector of coefficients.
        """

        blinder = Fr.rand()
        return self.pcs.commit(vec_c, blinder), blinder
    
    def inner_product_prove(self, \
            a_cm: G1Point, vec_b: list[Fr], c: Fr, vec_a: list[Fr], rho_a: Fr, \
            tr: MerlinTranscript, 
            debug=False) \
            -> IPA_Argument:
        """
        Prove an inner product of two vectors is correct.

            <(a0, a1,...,a_{n-1}), (b0, b1,...,b_{n-1})> = c
        
        Args:
            a_cm: the commitment to the vector a
            vec_b: the vector b
            c: the challenge scalar
            vec_a: the vector a
            rho_a: the blinding factor for the commitment to vec_a
            tr: the Merlin transcript to use for the proof
            debug: whether to print debug information
        Returns:
            an IPA_Argument tuple
        """
        n = len(vec_a)
        assert len(self.pcs.pp[0]) >= 2 * n + 1, f"EROR: len(pcs.pp) = {len(self.pcs.pp[0])}, while len(vec_a) = {len(vec_a)}"
        assert len(vec_b) == n, f"EROR: len(vec_b) = {len(vec_b)}, while len(vec_a) = {len(vec_a)}"

        if debug:
            print(f"prove> n: {n}")
        
        rng = random.Random(b"schnorr-1folding-commit")

        G = self.pcs.pp[0][:n]
        U = self.pcs.pp[0][-1]
        H = self.pcs.pp[1]

        tr.append_message(b"a_cm", str(a_cm).encode())
        tr.append_message(b"vec_b", str(vec_b).encode())
        tr.append_message(b"c", str(c).encode())

        # Round 1:   gamma <~ Fr 

        # WARN: challenge should be 32 bytes long, here we use 1 byte for debugging
        gamma = Fr.from_bytes(tr.challenge_bytes(b"gamma", 1))

        Ugamma = ec_mul(U, gamma)
        P = a_cm + ec_mul(Ugamma, c)
        PLR = []
        rho = rho_a

        def recursive_split_and_fold(G: list[G1Point], vec_a: list[Fr], vec_b: list[Fr], rho: Fr, P: G1Point) -> IPA_Argument:
            if len(vec_a) == 1:
                assert len(vec_a) == len(vec_b) == len(G) == 1, "EROR: len(vec_a) and len(vec_b) should be 1"
                a0 = vec_a[0]
                b0 = vec_b[0]
                G0 = G[0]

                # Round 4:  R -> 
                G_new = G0 + ec_mul(Ugamma, b0)
                r, rho_r = Fr.rands(rng, 2)
                R = ec_mul(G_new, r) + ec_mul(H, rho_r)
                tr.append_message(b"R", str(R).encode())

                # Round 5:  zeta <~ Fr
                zeta = Fr.from_bytes(tr.challenge_bytes(b"zeta", 1))
                if debug:
                    print(f"prove> zeta: {zeta}")

                # Round 6:  z ->  
                z = r + zeta * a0
                z_r = rho_r + zeta * rho
            
                # Debug
                if debug:
                    lhs = self.pcs.commit_with_pp([G_new], [z])
                    rhs = P + ec_mul(G_new, r) + ec_mul(P, zeta)
                    if lhs == rhs:
                        print(f"prove> [z]_(G_new) == pcs.commit_with_pp(G, vec_z) ok ")
                    else:
                        print(f"prove> Z == pcs.commit_with_pp(G, vec_z) failed ")

                return (n, PLR, R, z, z_r)

            half = len(vec_a) // 2
            G1 = G[:half]
            G2 = G[half:]
            as1 = vec_a[:half]
            as2 = vec_a[half:]
            bs1 = vec_b[:half]
            bs2 = vec_b[half:]
            rho_L, rho_R = Fr.rands(rng, 2)

            # Round 2:   PL, PR, ->
            PL = self.pcs.commit_with_pp(G1, as2) + ec_mul(Ugamma, ipa(as2, bs1)) + ec_mul(H, rho_L)
            PR = self.pcs.commit_with_pp(G2, as1) + ec_mul(Ugamma, ipa(as1, bs2)) + ec_mul(H, rho_R)
            PLR.insert(0, (PL, PR))

            tr.append_message(b"PL", str(PL).encode())
            tr.append_message(b"PR", str(PR).encode())

            # Round 3:   mu <~ Fr
            mu = Fr.from_bytes(tr.challenge_bytes(b"mu", 1))
            if debug:
                print(f"prove> mu: {mu}")
            vec_a = [as1[i] + as2[i] * mu for i in range(half)]
            vec_b = [bs1[i] + bs2[i] * mu.inv() for i in range(half)]
            rho += rho_L * mu + rho_R * mu.inv()
            
            G = [G1[i] + ec_mul(G2[i], mu.inv()) for i in range(half)]

            # Debug
            if debug:
                lhs = self.pcs.commit_with_pp(G, vec_a) + ec_mul(Ugamma, ipa(vec_a, vec_b)) + ec_mul(H, rho)
                P += ec_mul(PL, mu) + ec_mul(PR, mu.inv())
                if lhs == P:
                    print(f"prove> [vec_a]_(G) + [<vec_a, vec_b>]_(H) == P + mu*PL + mu^(-1)*PR ok ")
                else:
                    print(f"prove> [vec_a]_(G) + [<vec_a, vec_b>]_(H) == P + mu*PL + mu^(-1)*PR failed ")
            
            return recursive_split_and_fold(G, vec_a, vec_b, rho, P)
        
        return recursive_split_and_fold(G, vec_a, vec_b, rho, P)

        

    def inner_product_verify(self, a_cm: G1Point, vec_b: Fr, c: Fr, arg: IPA_Argument, tr: MerlinTranscript, debug=False) -> bool:
        """
        Verify an inner product argument.

            <(a0, a1,...,a_{n-1}), (b0, b1,...,b_{n-1})> = c

        Args:
            a_cm: the commitment to the vector a
            vec_b: the vector b
            c: the challenge scalar
            arg: the IPA_UNI_Argument (proof transcript)
            tr: the Merlin transcript to use for the proof
            debug: whether to print debug information
        """

        n, PLR, R, z, z_r = arg

        tr.append_message(b"a_cm", str(a_cm).encode())
        tr.append_message(b"vec_b", str(vec_b).encode())
        tr.append_message(b"c", str(c).encode())

        G = self.pcs.pp[0][:n]
        U = self.pcs.pp[0][-1]
        H = self.pcs.pp[1]

        # Round 1:   gamma <~ Fr 

        # WARN: challenge should be 32 bytes long, here we use 1 byte for debugging
        gamma = Fr.from_bytes(tr.challenge_bytes(b"gamma", 1))
        if debug:
            print(f"verify> gamma: {gamma}")

        Ugamma = ec_mul(U, gamma)
        P = a_cm + ec_mul(Ugamma, c)

        # Round 2:   PL, PR, ->
        round = 0
        half = n // 2
        while half > 0:
            PL, PR = PLR.pop()

            tr.append_message(b"PL", str(PL).encode())
            tr.append_message(b"PR", str(PR).encode())

            # Round 3:   mu <~ Fr
            mu = Fr.from_bytes(tr.challenge_bytes(b"mu", 1))
            if debug:
                print(f"verify> mu: {mu}")

            G1 = G[:half]
            G2 = G[half:]
            bs1 = vec_b[:half]
            bs2 = vec_b[half:]
            G = [G1[i] + ec_mul(G2[i], mu.inv()) for i in range(half)]
            vec_b = [bs1[i] + mu.inv() * bs2[i] for i in range(half)]
            
            # print(f"verify> G[{round}]: {G}")

            # Z_1 ?= Z + x * AL + x^{-1} * AR
        
            P += ec_mul(PL, mu) + ec_mul(PR, mu.inv())
            half = half // 2
            round += 1
        
        assert len(G) == len(vec_b) == 1, "EROR: len(vec_a) and len(vec_b) should be 1"
        G0 = G[0]
        b0 = vec_b[0]

        # Round 4:  R -> 
        tr.append_message(b"R", str(R).encode())

        # Round 5:  zeta <~ Fr
        zeta = Fr.from_bytes(tr.challenge_bytes(b"zeta", 1))
        if debug:
            print(f"verify> zeta: {zeta}")

        # Round 6:  z ->  
        
        G_new = G0 + ec_mul(Ugamma, b0)
        rhs = R + ec_mul(P, zeta)
        lhs = self.pcs.commit_with_pp([G_new, H], [z, z_r])

        return lhs == rhs

    def univariate_poly_eval_prove(self, \
            f_cm: G1Point, x: Fr, y: Fr, coeffs: list[Fr], rho: Fr, tr: MerlinTranscript, debug=False) \
            -> IPA_Argument:
        """
        Prove that a polynomial f(x) = y.

            f(X) = c0 + c1 * X + c2 * X^2 + ... + cn * X^n

        Args:
            f_cm: the commitment to the polynomial f(X)
            x: the challenge point
            y: the evaluation of f(x)
            vec_c: the coeffcient vector of the polynomial f(X)
            rho_c: the blinding factor for the commitment to vec_c
            tr: the Merlin transcript to use for the proof
            debug: whether to print debug information
        Returns:
            an IPA_PCS_Argument tuple
        """
        n = len(coeffs)
        vec_x = [x**i for i in range(n)]
        arg = self.inner_product_prove(f_cm, vec_x, y, coeffs, rho, tr, debug)
        return arg

        
    def univariate_poly_eval_verify(self, f_cm: G1Point, x: Fr, y: Fr, arg: IPA_Argument, tr: MerlinTranscript, debug=False) -> bool:
        """
        Verify an evaluation argument for a polynomial f, st. f(x) = y.

            f(X) = c0 + c1 * X + c2 * X^2 + ... + cn * X^n

        Args:
            f_cm: the commitment to the polynomial f(X)
            x: the challenge point
            y: the evaluation of f(x)
            arg: the IPA_PCS_Argument (proof transcript)
            tr: the Merlin transcript to use for the proof
            debug: whether to print debug information
        """
        n, PLR, R, z, z_r = arg
        vec_x = [x**i for i in range(n)]
        return self.inner_product_verify(f_cm, vec_x, y, arg, tr, debug)

    def mle_poly_eval_prove(self, f_cm: G1Point, us: list[Fr], v: Fr, evals: list[Fr], rho: Fr, tr: MerlinTranscript, debug=False) -> IPA_Argument:
        """
        Prove that an MLE polynomial f(u0, u1, ..., u_{n-1}) = v.

            f(X0, X1, ..., X_{n-1}) = a0 * eq(0, Xs) + a1 * eq(1, Xs) + ... + a_{n-1} * eq(n-1, Xs)

        Args:
            f_cm: the commitment to the MLE polynomial f(X0, X1, ..., X_{n-1})
            us: the evaluation point (u0, u1, ..., u_{n-1})
            v: the evaluation of f(u0, u1, ..., u_{n-1})
            evals: the evaluation of f(X0, X1, ..., X_{n-1}) over all 2^n points over the hypercube {0, 1}^n
            rho_c: the blinding factor for the commitment to vec_c
            tr: the Merlin transcript to use for the proof
            debug: whether to print debug information
        Returns:
            an IPA_PCS_Argument tuple
        """
        n = len(evals)
        arg = self.inner_product_prove(f_cm, us, v, evals, rho, tr, debug)
        return arg

        
    def mle_poly_eval_verify(self, \
            f_cm: G1Point, us: list[Fr], v: Fr, arg: IPA_Argument, tr: MerlinTranscript, debug=False) \
            -> bool:
        """
        Verify an evaluation argument for a polynomial f, st. f(x) = y.

            f(X0, X1, ..., X_{n-1}) = a0 * eq(0, Xs) + a1 * eq(1, Xs) + ... + a_{n-1} * eq(n-1, Xs)

        Args:
            f_cm: the commitment to the polynomial f(X)
            us: the evaluation point (u0, u1, ..., u_{n-1})
            v: the evaluation of f(u0, u1, ..., u_{n-1})
            arg: the IPA_PCS_Argument (proof transcript)
            tr: the Merlin transcript to use for the proof
            debug: whether to print debug information
        """
        n, PLR, R, z, z_r = arg
        return self.inner_product_verify(f_cm, us, v, arg, tr, debug)
    
def ipa(vec_a: list[Fr], vec_b: list[Fr]) -> Fr:
    n = len(vec_a)
    assert len(vec_b) == n
    return sum(a * b for a, b in zip(vec_a, vec_b))

def test_ipa_pcs():

    # initialize the PedersenCommitment and the IPA_PCS
    pcs = PedersenCommitment.setup(20)
    ipa_pcs = IPA_PCS(pcs)
    tr = MerlinTranscript(b"ipa-pcs")

    # A simple instance f(x) = y
    coeffs = [Fr(2), Fr(3), Fr(4), Fr(5), Fr(6), Fr(7), Fr(8), Fr(9)]
    x = Fr(4)
    vec_x = [x**i for i in range(len(coeffs))]
    y = ipa(coeffs, vec_x)

    # commit to the polynomial
    rho = Fr.rand()
    f_cm = pcs.commit_with_blinder(coeffs, rho)

    # fork the transcript for both prover and verifier
    tr_prover = tr.fork(b"prover")
    tr_verifier = tr.fork(b"verifier")

    # prover proves f(x) = y and sends an argument to the verifier
    arg = ipa_pcs.univariate_poly_eval_prove(f_cm, x, y, coeffs, rho, tr_prover, debug=True)
    print(f"arg: {arg}")

    # verifier verifies the argument
    verified = ipa_pcs.univariate_poly_eval_verify(f_cm, x, y, arg, tr_verifier, debug=True)
    print(f"verified: {verified}")

if __name__ == "__main__":
    test_ipa_pcs()