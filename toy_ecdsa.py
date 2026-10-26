"""toy_ecdsa.py - ECDSA on y^2 = x^3 + 7 over F_67 (group order 79). No crypto libraries.

Coordinates live mod P = 67, scalars mod N = 79. The point at infinity is `None` (O).
Everything is small enough to check by hand; pass `trace=[]` to scalar_mult / sign / verify
to collect every intermediate step.
"""
from __future__ import annotations

import hashlib
import secrets
from typing import Optional

P = 67  # field prime
A, B = 0, 7  # y^2 = x^3 + A x + B
Point = Optional[tuple[int, int]]  # None == O
O: Point = None

# --------------------------------------------------------------------------- modular arithmetic


def egcd(a: int, b: int) -> tuple[int, int, int]:
    """Extended Euclid: returns (g, x, y) with a*x + b*y = g = gcd(a, b)."""
    x0, y0, x1, y1 = 1, 0, 0, 1
    while b:
        q, a, b = a // b, b, a % b
        x0, x1 = x1, x0 - q * x1
        y0, y1 = y1, y0 - q * y1
    return a, x0, y0


def inv_mod(a: int, m: int) -> int:
    a %= m
    g, x, _ = egcd(a, m)
    if g != 1:
        raise ZeroDivisionError(f"{a} has no inverse mod {m}")
    return x % m


class Fp:
    """Field arithmetic mod P (thin helpers; values are plain ints in [0, P))."""

    @staticmethod
    def add(a, b): return (a + b) % P

    @staticmethod
    def sub(a, b): return (a - b) % P

    @staticmethod
    def mul(a, b): return (a * b) % P

    @staticmethod
    def inv(a): return inv_mod(a, P)

    @staticmethod
    def div(a, b): return (a * inv_mod(b, P)) % P

    @staticmethod
    def sqrt(a):
        """All square roots of a mod P (by search; P is tiny)."""
        return [y for y in range(P) if y * y % P == a % P]


# --------------------------------------------------------------------------- curve


def on_curve(Pt: Point) -> bool:
    if Pt is None:
        return True
    x, y = Pt
    return 0 <= x < P and 0 <= y < P and (y * y - (x ** 3 + A * x + B)) % P == 0


def enumerate_points() -> list[Point]:
    """All group elements: O first, then affine points sorted by (x, y)."""
    pts: list[Point] = [O]
    for x in range(P):
        for y in Fp.sqrt(x ** 3 + A * x + B):
            pts.append((x, y))
    return pts


def neg(Pt: Point) -> Point:
    return None if Pt is None else (Pt[0], (-Pt[1]) % P)


def point_add(P1: Point, P2: Point, trace: Optional[list] = None) -> Point:
    if P1 is None:
        return P2
    if P2 is None:
        return P1
    x1, y1 = P1
    x2, y2 = P2
    if x1 == x2 and (y1 + y2) % P == 0:  # P + (-P) (includes doubling a y=0 point)
        if trace is not None:
            trace.append(("add", P1, P2, None, O))
        return O
    if P1 == P2:  # doubling: lambda = (3x^2 + a) / 2y
        lam = Fp.div(3 * x1 * x1 + A, 2 * y1)
    else:  # chord: lambda = (y2 - y1) / (x2 - x1)
        lam = Fp.div(y2 - y1, x2 - x1)
    x3 = (lam * lam - x1 - x2) % P
    y3 = (lam * (x1 - x3) - y1) % P
    if trace is not None:
        trace.append(("dbl" if P1 == P2 else "add", P1, P2, lam, (x3, y3)))
    return (x3, y3)


def scalar_mult(k: int, Pt: Point, trace: Optional[list] = None) -> Point:
    """Left-to-right double-and-add."""
    if k < 0:
        return scalar_mult(-k, neg(Pt), trace)
    R: Point = O
    for bit in bin(k)[2:] if k else "":
        R = point_add(R, R, trace) if R is not None else R
        if bit == "1":
            R = point_add(R, Pt, trace) if R is not None else Pt
    return R


def point_order(Pt: Point) -> int:
    k, R = 1, Pt
    while R is not None:
        R = point_add(R, Pt)
        k += 1
    return k


def find_generator() -> Point:
    """Since the group order is prime, any non-identity point generates it; take the first."""
    return enumerate_points()[1]


N = len(enumerate_points())  # group order = 79 (prime)
G: Point = find_generator()  # (2, 22)

# --------------------------------------------------------------------------- ECDSA


def hash_to_int(msg: bytes | str) -> int:
    """z = leftmost bitlen(N) bits of SHA-256(msg), as ECDSA specifies (7 bits for N=79)."""
    if isinstance(msg, str):
        msg = msg.encode()
    h = int.from_bytes(hashlib.sha256(msg).digest(), "big")
    return h >> (256 - N.bit_length())


def keygen(d: Optional[int] = None) -> tuple[int, Point]:
    d = d if d is not None else 1 + secrets.randbelow(N - 1)
    if not 1 <= d < N:
        raise ValueError("private key must be in [1, N-1]")
    return d, scalar_mult(d, G)


def is_low_s(sig: tuple[int, int]) -> bool:
    return sig[1] <= N // 2


def normalize_low_s(sig: tuple[int, int]) -> tuple[int, int]:
    r, s = sig
    return (r, N - s) if s > N // 2 else (r, s)


def sign_hash(d: int, z: int, k: Optional[int] = None, low_s: bool = False,
              trace: Optional[dict] = None) -> tuple[int, int]:
    """Sign hash value z. If k is given it is used (for the nonce-reuse demo); else random."""
    while True:
        kk = k if k is not None else 1 + secrets.randbelow(N - 1)
        R = scalar_mult(kk, G)
        r = R[0] % N
        if r == 0:
            if k is not None:
                raise ValueError("r = 0 for this nonce")
            continue
        k_inv = inv_mod(kk, N)
        s = k_inv * (z + r * d) % N
        if s == 0:
            if k is not None:
                raise ValueError("s = 0 for this nonce")
            continue
        sig = (r, s)
        if low_s:
            sig = normalize_low_s(sig)
        if trace is not None:
            trace.update(k=kk, R=R, r=r, k_inv=k_inv, s_raw=s, sig=sig)
        return sig


def sign(d: int, msg: bytes | str, k: Optional[int] = None, low_s: bool = False) -> tuple[int, int]:
    return sign_hash(d, hash_to_int(msg), k, low_s)


def verify_hash(Q: Point, z: int, sig: tuple[int, int], require_low_s: bool = False,
                trace: Optional[dict] = None) -> bool:
    r, s = sig
    if not (1 <= r < N and 1 <= s < N):
        return False
    if require_low_s and not is_low_s(sig):
        return False
    if Q is None or not on_curve(Q):
        return False
    w = inv_mod(s, N)
    u1, u2 = z * w % N, r * w % N
    X = point_add(scalar_mult(u1, G), scalar_mult(u2, Q))
    if trace is not None:
        trace.update(w=w, u1=u1, u2=u2, X=X)
    return X is not None and X[0] % N == r


def verify(Q: Point, msg: bytes | str, sig: tuple[int, int], require_low_s: bool = False) -> bool:
    return verify_hash(Q, hash_to_int(msg), sig, require_low_s)


# --------------------------------------------------------------------------- nonce-reuse attack


def recover_from_nonce_reuse(Q: Point, z1: int, sig1: tuple[int, int],
                             z2: int, sig2: tuple[int, int]) -> tuple[int, int]:
    """Recover (d, k) from two signatures that used the same nonce.

    Low-s normalisation may have replaced s by N - s (i.e. k by -k) in either signature, so
    s1 = ±k^-1 (z1 + r d), s2 = ±k^-1 (z2 + r d). Try k = (z1 - z2) / (s1 ∓ s2), derive
    d = (s1 k - z1) / r and keep the candidate whose d*G equals the public key Q.
    """
    (r1, s1), (r2, s2) = sig1, sig2
    if r1 != r2:
        raise ValueError("different r: the nonce was not reused")
    r = r1
    for s2_signed in (s2, -s2):
        denom = (s1 - s2_signed) % N
        if denom == 0:
            continue
        k = (z1 - z2) * inv_mod(denom, N) % N
        if k == 0:
            continue
        d = (s1 * k - z1) * inv_mod(r, N) % N
        if d and scalar_mult(d, G) == Q:
            return d, k  # k is the effective nonce for sig1 (±original)
    raise ValueError("could not recover the key (are z1 and z2 equal mod N?)")


if __name__ == "__main__":
    print(f"curve y^2 = x^3 + 7 over F_{P}: {N} points, G = {G}, ord(G) = {point_order(G)}")
    d, Q = keygen(9)
    m1, m2 = "pay alice 5", "pay bob 9"
    k = 13
    s1, s2 = sign(d, m1, k), sign(d, m2, k)
    print("d =", d, "Q =", Q, "sig1 =", s1, "sig2 =", s2)
    for f1 in (False, True):
        for f2 in (False, True):
            a = (s1[0], N - s1[1]) if f1 else s1
            b = (s2[0], N - s2[1]) if f2 else s2
            print(f"flip1={f1!s:5} flip2={f2!s:5} ->", recover_from_nonce_reuse(
                Q, hash_to_int(m1), a, hash_to_int(m2), b))
