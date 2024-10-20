#!/usr/bin/env python3

from functools import reduce
from utils import log_2, pow_2, bits_le_with_width

class MLEPolynomial:
    def __init__(self, evals, num_var):
        self.evals = evals
        self.num_var = num_var

    def __repr__(self):
        return f"MLEPolynomial({self.evals}, {self.num_var})"
    
    def __getitem__(self, index):
        """
        Retrieve an evaluation using square bracket notation.

        Args:
            index (int): The index of the evaluation to retrieve.

        Returns:
            The evaluation at the given index.

        Raises:
            IndexError: If the index is out of range.
        """
        
        if 0 <= index < len(self.evals):
            return self.evals[index]
        else:
            raise IndexError("Evaluation index out of range")


    @classmethod
    def eqs_over_hypercube(cls, rs):
        k = len(rs)
        n = 1 << k
        evals = [1] * n
        half = 1
        for i in range(k):
            for j in range(half):
                evals[j+half] = evals[j] * rs[i]
                evals[j] = evals[j] - evals[j+half]
            half *= 2
        return evals
    
    @classmethod
    def eqs_over_hypercube_slow(cls, k, indeterminates):
        if k > 5:
            raise ValueError("k>5 isn't supported")
        xs = indeterminates[:k]
        n = 1 << k
        eqs = [1] * n
        for i in range(n):
            bs = bits_le_with_width(i, k)
            eqs[i] = reduce(lambda v, j: v * ((1 - xs[j]) * (1 - bs[j]) + xs[j] * bs[j]), range(k), 1)
        return eqs

    @classmethod
    def from_coeffs(cls, coeffs, num_var):
        return cls(cls.compute_evals_from_coeffs(coeffs), num_var)
    
    @classmethod
    def ntt_core(cls, vs, twiddle):
        n = len(vs)
        k = log_2(n)
        half = 1
        for i in range(k):
            for j in range(0, n, 2*half):
                for l in range(j, j+half):
                    vs[l+half] = vs[l+half] + twiddle * vs[l]
            half <<= 1
        return vs

    @classmethod
    def compute_evals_from_coeffs(cls, f_coeffs):
        """
        Compute the evaluations of the polynomial from the coefficients.
            Time: O(n * log(n))
        """
        return cls.ntt_core(f_coeffs, 1)

    @classmethod
    def compute_coeffs_from_evals(cls, f_evals):
        """
        Compute the evaluations of the polynomial from the coefficients.
            Time: O(n * log(n))
        """
        return cls.ntt_core(f_evals, -1)
    
    @classmethod
    def evaluate_from_evals(cls, evals, zs):
        f = evals

        half = len(f) >> 1
        for z in zs:
            even = f[::2]
            odd = f[1::2]
            f = [even[i] + z * (odd[i] - even[i]) for i in range(half)]
            half >>= 1
        return f[0]
    
    @classmethod
    def evaluate_from_evals_2(cls, evals, zs):
        k = len(zs)
        f = evals

        half = len(f) >> 1
        for i in range(k):
            u = zs[k-i-1]

            f = [(1-u) * f[j] + u * f[j+half] for j in range(half)]
            half >>= 1
        
        return f[0]
    
    def evaluate(self, zs: list):
        """
        Evaluate the MLE polynomial at the given points.

        Args:
            zs (list): List of points to evaluate the polynomial at.

        Returns:
            int: The evaluated value of the polynomial at the given points.
        """
        if not isinstance(zs, list):
            raise TypeError("Input zs must be a list.")
        
        return self.evaluate_from_evals(self.evals, zs)
    
    @staticmethod
    def evaluate_from_coeffs(coeffs, zs):
        z = len(zs)
        f = coeffs

        half = len(f) >> 1
        for z in zs:
            even = f[::2]
            odd = f[1::2]
            f = [even[i] + z * odd[i] for i in range(half)]
            half >>= 1
        return f[0]

    def decompose_by_div(self, point):
        """
        Divide an MLE at the point: [X_0, X_1, ..., X_{n-1}] in O(N) (Linear!)

        Args:
            poly (MLEPolynomial): the MLE polynomial to be divided
            point (list): the point to divide the polynomial

        Returns:
        list: quotients, the list of MLEs
        """
        assert self.num_var == len(point), "Number of variables must match the point"
        e = self.evals.copy()
        k = self.num_var
        quotients = []
        half = pow_2(k - 1)
        for i in range(k):
            q = [0] * half
            for j in range(half):
                q[j] = e[j + half] - e[j]
                e[j] = e[j] * (1 - point[k-i-1]) + e[j + half] * point[k-i-1]
            quotients.insert(0, MLEPolynomial(q, k-i-1))
            half >>= 1

        return quotients, e[0]
    
    @staticmethod
    def decompose_by_div_from_coeffs(coeffs: list, point: list) -> list:
        """
        Decompose the MLE polynomial into quotients by division.

            f(X0,X1,...,X_{n-1}) = (X0-u0) * q0 
                                + (X1-u1) * q1(X0) + ... 
                                + (X_{n-1} - u_{n-1}) * q_{n-1}(X0,X1,...,X_{n-2})
                                + f(u0, u1, ..., u_{n-1})
        
        Args:
            coeffs (list[Field]): The coefficients of the MLE polynomial to be divided
            point (list[Field]): The point to divide the polynomial

        Returns:
            list[Field]: Quotients [q_0, q_1, ..., q_{n-1}] where q_i(X_0, X_1, ..., X_{i-1})
        """
        
        k = len(point)
        n = len(coeffs)
        assert n == pow_2(k), "Number of variables must match the point"
        
        coeffs = coeffs.copy()
        quotients = []
        half = pow_2(k - 1)
        for i in range(k):
            quo_coeffs = [0] * half
            for j in range(half):
                quo_coeffs[j] = coeffs[j + half]
                coeffs[j] = coeffs[j] + point[k-i-1] * coeffs[j + half]
            quotients.insert(0, quo_coeffs)
            half >>= 1

        return quotients, coeffs[0]
    
    def mul_quotients(quotient, remainder, p):
        """
        r: current remainder
        q: current quotient
        p: current point

        last_remainder
        = r + (xi - p) * q
        = r - p * q + xi * q
        = (r - p * q) * (1 - xi) + (r - (p - 1) * q) * xi
        """

        assert isinstance(quotient, MLEPolynomial), "quotient must be an MLEPolynomial"
        assert isinstance(remainder, MLEPolynomial), "remainder must be an MLEPolynomial"

        half = len(quotient.evals)
        result = [0] * 2 * half
        for i, (q, r) in enumerate(zip(quotient.evals, remainder.evals)):
            result[i] = r - p * q
            result[i + half] = r - (p - 1) * q
        return MLEPolynomial(result, quotient.num_var + 1)

