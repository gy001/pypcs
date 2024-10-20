#!/usr/bin/env python3

# WARNING: This implementation may contain bugs and has not been audited. 
# It is only for educational purposes. DO NOT use it in production.

from utils import log_2, next_power_of_two
from pypcs.curve import Fp, Fr, ec_mul, G1Point
from merlin.merlin_transcript import MerlinTranscript

from pedersen import PedersenCommitment
from mle import MLEPolynomial

# WARNING: 
#   1. For demonstration, we deliberately use an insecure random number 
#      generator, random.Random. To generate secure randomness, use 
#      the standard library `secrets` instead.
#        
#      See more here: https://docs.python.org/3/library/secrets.html
#
#   2. Challenges are only 1 byte long for simplicity, which is not secure.

import random

# Implementation of Hyrax-PCS with sqrt(n) commitments from Section 6.1 in [WTSTW17]:
#
#   Hyrax: https://eprint.iacr.org/2017/1132.pdf
#
# The proof size is sqrt(n), and the verification time is O(sqrt(n)).
#
# NOTE: This pcs can only be used for some randomly chosen challenge points after 
#       the sqrt(n) commitments are sent to the verifier.

# TODO:
# - add options for the blinders
# - add batch proving and verifying


IPA_Argument = tuple[int,G1Point, G1Point, G1Point, list[Fr]]

class IPA_PCS:

    pcs: PedersenCommitment
    rng: random.Random
    debug: bool

    def __init__(self, pcs: PedersenCommitment):
        """
        Args:
            pcs: the PedersenCommitment instance to use for the proof
        """
        self.pcs = pcs
        self.rng = random.Random("ipa-pcs")
        self.debug = False

    def commit(self, vec_a: list[Fr]) -> tuple[list[G1Point], list[Fr]]:
        """
        Commit to a vector of coefficients.
        """
        logn = log_2(len(vec_a))
        half = logn // 2
        row, col = 2**half, 2**(logn - half)
        
        print(f"row: {row}, col: {col}")

        blinders = Fr.rands(self.rng, col)

        a_cm = []
        for i in range(row):
            a_row = vec_a[i*row:(i+1)*row]
            a_cm += [self.pcs.commit_with_blinder(a_row, blinders[i])]
        return a_cm, blinders
    
    def batch_inner_product_prove(self, cm_a: list[G1Point], vec_a: list[Fr], blinders: list[Fr], \
                        vec_b0: list[Fr], vec_b1: list[Fr], v: Fr, tr: MerlinTranscript):
        n = len(vec_a)
        col = len(vec_b0)
        row = len(vec_b1)
        assert col * row == n, \
            f"vec_b0 and vec_b1 must have {n} elements, but got {col} and {row}"
        assert len(blinders) == col, f"blinders must have {col} elements, but got {len(blinders)}"

        # G = self.pcs.pp[:col]
        # H = self.pcs.pp[-2]

        f_folded = [0] * col
        f_folded_cm = G1Point.zero()
        blinders_folded = Fr(0)
        for i in range(row):
            for j in range(col):
                f_folded[j] += vec_b1[i] * vec_a[i * row + j]
            blinders_folded += vec_b1[i] * blinders[i]
            f_folded_cm += ec_mul(cm_a[i], vec_b1[i])
        
        if self.debug:
            if ipa(f_folded, vec_b0) == v:
                print(f"batch_inner_product_prove> ipa(f_folded, vec_b0) == v, v={v}")
            else:
                print(f"batch_inner_product_prove> ipa(f_folded, vec_b0) must be {v}, but got {ipa(f_folded, vec_b0)}")

            if self.pcs.commit_with_blinder(f_folded, blinders_folded) == f_folded_cm:
                print(f"batch_inner_product_prove> cm(f_folded) + cm(blinders_folded) == f_folded_cm")
            else:
                print(f"batch_inner_product_prove> cm(G, f_folded) + cm(H, blinders_folded) must be {f_folded_cm}, but got {self.pcs.commit_with_pp(G, f_folded) + ec_mul(H, blinders_folded)}")

        arg = self.inner_product_prove(f_folded_cm, f_folded, blinders_folded, vec_b0, v, tr)
        return arg
    
    def batch_inner_product_verify(self, cm_a: list[G1Point], vec_b0: list[Fr], vec_b1: list[Fr], v: Fr, \
                                   arg: IPA_Argument, tr: MerlinTranscript) -> bool:

        col = len(vec_b0)
        row = len(vec_b1)

        f_folded_cm = G1Point.zero()
        for i in range(row):
            f_folded_cm += ec_mul(cm_a[i], vec_b1[i])
        verified = self.inner_product_verify(f_folded_cm, vec_b0, v, arg, tr)
        return verified

    def inner_product_prove(self, cm_a: G1Point, vec_a: list[Fr], blinder_a: Fr, vec_b: list[Fr], c: Fr, \
                            tr: MerlinTranscript) -> tuple[G1Point, G1Point, G1Point, list[Fr], Fr, Fr]:
        """
        Prove an inner product argument.

            <(a0, a1,...,a_{n-1}), (b0, b1,...,b_{n-1})> = c

        Args:
            cm_a: the commitment to the vector a
            vec_a: the vector a
            blinder_a: the blinder for the commitment to a
            vec_b: the vector b
            c: the challenge scalar
            tr: the Merlin transcript to use for the proof
        Returns:
            the challenge scalar c
        """
        n = len(vec_a)

        if self.debug:
            if cm_a == self.pcs.commit_with_blinder(vec_a, blinder_a):
                print(f"inner_product_prove> cm_a == self.pcs.commit_with_blinder(vec_a, blinder_a)")
            else:
                raise ValueError(f"inner_product_prove> cm_a must be {self.pcs.commit(vec_a, blinder_a)}, but got {cm_a}")
        
        tr.append_message(b"cm_a", str(cm_a).encode())
        tr.append_message(b"vec_b", str(vec_b).encode())
        tr.append_message(b"c", str(c).encode())

        # Round 1:
        ra = Fr.rands(self.rng, n)
        ra_rho = Fr.rand(self.rng)

        Ra = self.pcs.commit_with_blinder(ra, ra_rho)

        e0 = sum([ra[i] * vec_b[i] for i in range(n)])
        e0_rho = Fr.rand(self.rng)
        E0 = self.pcs.commit_with_blinder([e0], e0_rho)
        e1_rho = Fr.rand(self.rng)
        E1 = self.pcs.commit_with_blinder([Fr.zero()], e1_rho)

        # Round 2:
        tr.append_message(b"Ra", str(Ra).encode())
        tr.append_message(b"E0", str(E0).encode())
        tr.append_message(b"E1", str(E1).encode())
        mu = Fr.from_bytes(tr.challenge_bytes(b"mu", 1))
        if self.debug:
            print(f"inner_product_prove> mu: {mu}")

        # Round 3:
        za = [ra[i] + mu * vec_a[i] for i in range(n)]
        za_rho = ra_rho + mu * blinder_a
        ze = e0_rho + mu * e1_rho

        if self.debug:
            print(f"inner_product_prove> za: {za}")
            print(f"inner_product_prove> za_rho: {za_rho}")
            print(f"inner_product_prove> ze: {ze}")
            if Ra + ec_mul(cm_a, mu) == self.pcs.commit_with_blinder(za, za_rho):
                print(f"inner_product_prove> Ra + ec_mul(cm_a, mu) == self.pcs.commit(za, za_rho)")
            else:
                raise ValueError(f"inner_product_prove> Ra + ec_mul(cm_a, mu) must be {self.pcs.commit_with_blinder(za, za_rho)}, but got {Ra + ec_mul(cm_a, mu)}")

        return (Ra, E0, E1, za, za_rho, ze)

    def inner_product_verify(self, cm_a: G1Point, vec_b: list[Fr], c: Fr, arg: IPA_Argument, \
                             tr: MerlinTranscript) -> bool:
        """
        Verify an inner product argument.

            <(a0, a1,...,a_{n-1}), (b0, b1,...,b_{n-1})> = c

        Args:
            cm_a: the commitment to the vector a
            vec_b: the vector b
            c: the challenge scalar
            arg: the IPA_UNI_Argument (proof transcript)
            tr: the Merlin transcript to use for the proof
            debug: whether to print debug information
        """

        tr.append_message(b"cm_a", str(cm_a).encode())
        tr.append_message(b"vec_b", str(vec_b).encode())
        tr.append_message(b"c", str(c).encode())

        Ra, E0, E1, za, za_rho, ze = arg
        n = len(za)

        # Round 1:
        tr.append_message(b"Ra", str(Ra).encode())
        tr.append_message(b"E0", str(E0).encode())
        tr.append_message(b"E1", str(E1).encode())

        # Round 2:
        mu = Fr.from_bytes(tr.challenge_bytes(b"mu", 1))
        if self.debug:
            print(f"inner_product_verify> mu: {mu}")

        # Round 3:
        ab = sum([za[i] * vec_b[i] for i in range(n)])
        cond0 = Ra + ec_mul(cm_a, mu) == self.pcs.commit_with_blinder(za, za_rho)
        C = self.pcs.commit_with_blinder([c], Fr.zero())
        cond1 = E0 + ec_mul(E1, mu) + ec_mul(C, mu) == self.pcs.commit_with_blinder([ab], ze)
        print(f"inner_product_verify> cond0: {cond0}")
        print(f"inner_product_verify> cond1: {cond1}")
        return cond0 and cond1

    def univariate_poly_eval_prove(self, \
            cm_f: list[G1Point], x: Fr, y: Fr, coeffs: list[Fr], blinders_f: list[Fr], tr: MerlinTranscript) \
            -> IPA_Argument:
        """
        Prove that a polynomial f(x) = y.

            f(X) = c0 + c1 * X + c2 * X^2 + ... + cn * X^n

        Args:
            cm_f: the commitment to the polynomial f(X)
            x: the challenge point
            y: the evaluation of f(x)
            coeffs: the coeffcient vector of the polynomial f(X)
            blinders_f: the blinding factors for the commitment to coeffs
            tr: the Merlin transcript to use for the proof
        Returns:
            an IPA_PCS_Argument tuple
        """
        n = next_power_of_two(len(coeffs))
        logn = log_2(n)
        logn_half = logn // 2
        assert len(blinders_f) == 2**logn_half, f"blinders_f must have {2**logn_half} elements, but got {len(blinders_f)}"

        x_powers_l = [x**(i) for i in range(2**logn_half)]
        x_powers_r = [(x**(2**logn_half))**(i) for i in range(2**logn_half)]
        
        if self.debug:
            x_powers = [x**(i) for i in range(n)]
            assert y == ipa(coeffs, x_powers)

        arg = self.batch_inner_product_prove(cm_f, coeffs, blinders_f, x_powers_l, x_powers_r, y, tr)
        return (len(coeffs), arg)

        
    def univariate_poly_eval_verify(self, cm_f: G1Point, x: Fr, y: Fr, arg: IPA_Argument, tr: MerlinTranscript) -> bool:
        """
        Verify an evaluation argument for a polynomial f, st. f(x) = y.

            f(X) = c0 + c1 * X + c2 * X^2 + ... + cn * X^n

        Args:
            f_cm: the commitment to the polynomial f(X)
            x: the challenge point
            y: the evaluation of f(x)
            arg: the IPA_PCS_Argument (proof transcript)
            tr: the Merlin transcript to use for the proof
        """
        n, inner_arg = arg
        logn_half = log_2(n) // 2

        x_powers_l = [x**(i) for i in range(2**logn_half)]
        x_powers_r = [(x**(2**logn_half))**(i) for i in range(2**logn_half)]

        return self.batch_inner_product_verify(cm_f, x_powers_l, x_powers_r, y, inner_arg, tr)

    def mle_poly_eval_prove(self, cm_f: G1Point, us: list[Fr], v: Fr, f: MLEPolynomial, blinders_f: list[Fr], \
                            tr: MerlinTranscript) -> IPA_Argument:
        """
        Prove that an MLE polynomial f(u0, u1, ..., u_{n-1}) = v.

            f(X0, X1, ..., X_{n-1}) = a0 * eq(0, Xs) + a1 * eq(1, Xs) + ... + a_{n-1} * eq(n-1, Xs)

        Args:
            cm_f: the commitment to the MLE polynomial f(X0, X1, ..., X_{n-1})
            us: the evaluation point (u0, u1, ..., u_{n-1})
            v: the evaluation of f(u0, u1, ..., u_{n-1})
            f: the MLE polynomial
            rho_f: the blinding factor for the commitment to f
            tr: the Merlin transcript to use for the proof
            debug: whether to print debug information
        Returns:
            an IPA_PCS_Argument tuple
        """
        n = 2**f.num_var
        us_l = us[:f.num_var//2]
        us_r = us[f.num_var//2:]
        vec_eq_l = MLEPolynomial.eqs_over_hypercube(us_l)
        vec_eq_r = MLEPolynomial.eqs_over_hypercube(us_r)
        vec_eq = MLEPolynomial.eqs_over_hypercube(us)
        assert v == ipa(f.evals, vec_eq)
        arg = self.batch_inner_product_prove(cm_f, f.evals, blinders_f, vec_eq_l, vec_eq_r, v, tr)
        return arg
        
    def mle_poly_eval_verify(self, cm_f: G1Point, us: list[Fr], v: Fr, arg: IPA_Argument, tr: MerlinTranscript) \
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
        """
        n = len(us)
        us_l = us[:n//2]
        us_r = us[n//2:]
        vec_eq_l = MLEPolynomial.eqs_over_hypercube(us_l)
        vec_eq_r = MLEPolynomial.eqs_over_hypercube(us_r)
        verified = self.batch_inner_product_verify(cm_f, vec_eq_l, vec_eq_r, v, arg, tr)
        return verified
    
def ipa(vec_a: list[Fr], vec_b: list[Fr]) -> Fr:
    n = len(vec_a)
    assert len(vec_b) == n
    return sum(a * b for a, b in zip(vec_a, vec_b))

def test_ipa_uni_pcs():

    # initialize the PedersenCommitment and the IPA_PCS
    cms = PedersenCommitment.setup(20)
    ipa_pcs = IPA_PCS(cms)
    ipa_pcs.debug = True

    tr = MerlinTranscript(b"ipa-pcs")

    # A simple instance f(x) = y
    coeffs = [Fr(2), Fr(3), Fr(4), Fr(5), Fr(6), Fr(7), Fr(8), Fr(9), \
             Fr(10), Fr(11), Fr(12), Fr(13), Fr(14), Fr(15), Fr(16), Fr(17)]
    x = Fr(4)
    vec_x = [x**i for i in range(len(coeffs))]
    y = ipa(coeffs, vec_x)

    # commit to the polynomial
    cm_f, blinders_f = ipa_pcs.commit(coeffs)

    # fork the transcript for both prover and verifier
    tr_prover = tr.fork(b"prover")
    tr_verifier = tr.fork(b"verifier")

    # prover proves f(x) = y and sends an argument to the verifier
    arg = ipa_pcs.univariate_poly_eval_prove(cm_f, x, y, coeffs, blinders_f, tr_prover)
    print(f"arg: {arg}")

    # verifier verifies the argument
    verified = ipa_pcs.univariate_poly_eval_verify(cm_f, x, y, arg, tr_verifier)
    print(f"uni_polycom verified: {verified}")
    assert verified, "univariate polynomial evaluation verification failed"

def test_ipa_mle_pcs():

    # initialize the PedersenCommitment and the IPA_PCS
    pcs = PedersenCommitment.setup(20)
    ipa_pcs = IPA_PCS(pcs)
    ipa_pcs.debug = True

    tr = MerlinTranscript(b"ipa-mle-pcs")

    # A simple instance f(x) = y
    f = MLEPolynomial([Fr(2), Fr(3), Fr(4), Fr(5), Fr(6), Fr(7), Fr(8), Fr(9), \
                       Fr(10), Fr(11), Fr(10), Fr(11), Fr(6), Fr(7), Fr(8), Fr(9)], 4)
    us = [Fr(2), Fr(3), Fr(3), Fr(2)]
    v = f.evaluate(us)
    print(f"v: {v}")

    # commit to the polynomial
    cm_f, rho_f = ipa_pcs.commit(f.evals)

    # fork the transcript for both prover and verifier
    tr_prover = tr.fork(b"prover")
    tr_verifier = tr.fork(b"verifier")

    # prover proves f(x) = y and sends an argument to the verifier
    arg = ipa_pcs.mle_poly_eval_prove(cm_f, us, v, f, rho_f, tr_prover)
    print(f"arg: {arg}")

    # verifier verifies the argument
    verified = ipa_pcs.mle_poly_eval_verify(cm_f, us, v, arg, tr_verifier)
    print(f"mle_polycom verified: {verified}")
    assert verified, "MLE polynomial evaluation verification failed"

def test_inner_product():

    # initialize the PedersenCommitment and the IPA_PCS
    cms = PedersenCommitment.setup(20)
    ipa_pcs = IPA_PCS(cms)
    ipa_pcs.debug = False

    tr = MerlinTranscript(b"ipa-mle-pcs")

    # A simple instance f(x) = y
    vec_b =[Fr(6), Fr(7), Fr(8), Fr(9)]
    vec_a = [Fr(1), Fr(2), Fr(3), Fr(4)]
    c = ipa(vec_a, vec_b)
    print(f"inner product: {c}")

    # commit to the polynomial
    rho_a = Fr.rand()
    cm_a = cms.commit_with_blinder(vec_a, rho_a)

    # fork the transcript for both prover and verifier
    tr_prover = tr.fork(b"prover")
    tr_verifier = tr.fork(b"verifier")

    # prover proves f(x) = y and sends an argument to the verifier
    arg = ipa_pcs.inner_product_prove(cm_a, vec_a, rho_a, vec_b, c, tr_prover)
    print(f"arg: {arg}")

    # verifier verifies the argument
    verified = ipa_pcs.inner_product_verify(cm_a, vec_b, c, arg, tr_verifier)
    print(f"inner_product verified: {verified}")
    assert verified, "inner product verification failed"

if __name__ == "__main__":
    test_inner_product()
    test_ipa_mle_pcs()
    test_ipa_uni_pcs()

