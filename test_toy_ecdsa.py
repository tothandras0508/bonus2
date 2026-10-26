import itertools

import pytest

import toy_ecdsa as t
from toy_ecdsa import G, N, O, P


# ------------------------------------------------------------------ field


def test_inverse_mod_p_and_n():
    for m in (P, N):
        for a in range(1, m):
            assert a * t.inv_mod(a, m) % m == 1
    with pytest.raises(ZeroDivisionError):
        t.inv_mod(0, P)


def test_field_helpers():
    assert t.Fp.add(60, 10) == 3
    assert t.Fp.sub(3, 10) == 60
    assert t.Fp.mul(22, 22) == 484 % 67 == 15
    assert t.Fp.div(1, 2) == 34  # 2 * 34 = 68 = 1 mod 67


# ------------------------------------------------------------------ group


def test_curve_has_79_elements():
    pts = t.enumerate_points()
    assert len(pts) == 79 and N == 79
    assert pts[0] is O and len([p for p in pts if p is not None]) == 78
    assert len(set(pts)) == 79 and all(t.on_curve(p) for p in pts)


def test_group_order_is_prime():
    assert all(N % q for q in range(2, N))


def test_generator_order():
    assert G == (2, 22) and t.on_curve(G)
    assert t.scalar_mult(N, G) is O
    assert t.point_order(G) == N
    assert all(t.scalar_mult(k, G) is not O for k in range(1, N))


def test_every_nonidentity_point_generates():
    for Pt in t.enumerate_points()[1:]:
        assert t.scalar_mult(N, Pt) is O and t.scalar_mult(1, Pt) == Pt
    multiples = {t.scalar_mult(k, G) for k in range(N)}
    assert multiples == set(t.enumerate_points())


def test_point_addition_laws():
    pts = t.enumerate_points()
    some = pts[:12]
    for a, b in itertools.product(some, repeat=2):
        assert t.point_add(a, b) == t.point_add(b, a)
        assert t.on_curve(t.point_add(a, b))
    for a, b, c in itertools.product(pts[1:6], repeat=3):
        assert t.point_add(t.point_add(a, b), c) == t.point_add(a, t.point_add(b, c))
    for a in pts:
        assert t.point_add(a, O) == a
        assert t.point_add(a, t.neg(a)) is O


def test_double_and_add_matches_repeated_addition():
    R = O
    for k in range(0, 2 * N):
        assert t.scalar_mult(k, G) == R
        R = t.point_add(R, G)
    assert t.scalar_mult(-5, G) == t.neg(t.scalar_mult(5, G))


def test_hand_values():
    # 2G: lambda = 3*2^2 / (2*22) = 12/44 = 12 * 44^-1 mod 67
    trace = []
    assert t.scalar_mult(2, G, trace) == t.point_add(G, G)
    op, P1, P2, lam, R = trace[0]
    assert op == "dbl" and lam == 12 * t.inv_mod(44, P) % P
    assert R == ((lam * lam - 4) % P, (lam * (2 - R[0]) - 22) % P)


# ------------------------------------------------------------------ ECDSA


@pytest.fixture
def key():
    return t.keygen(9)


def test_sign_verify_roundtrip(key):
    d, Q = key
    for k in range(1, N):
        try:
            sig = t.sign(d, "hello", k=k)
        except ValueError:
            continue
        assert t.verify(Q, "hello", sig)


def test_signature_fails_for_other_message(key):
    d, Q = key
    m1, m2 = "pay alice 5", "pay bob 9"
    assert t.hash_to_int(m1) % N != t.hash_to_int(m2) % N
    sig = t.sign(d, m1, k=13)
    assert t.verify(Q, m1, sig)
    assert not t.verify(Q, m2, sig)


def test_signature_fails_for_other_key(key):
    d, Q = key
    sig = t.sign(d, "hello", k=13)
    _, Q2 = t.keygen(10)
    assert not t.verify(Q2, "hello", sig)


def test_high_s_counterpart_verifies(key):
    d, Q = key
    for k in (3, 13, 40, 77):
        r, s = t.sign(d, "malleable", k=k)
        assert t.verify(Q, "malleable", (r, s))
        assert t.verify(Q, "malleable", (r, N - s))
        low = t.normalize_low_s((r, s))
        assert t.is_low_s(low) and t.verify(Q, "malleable", low, require_low_s=True)
        high = (r, max(s, N - s))
        assert not t.verify(Q, "malleable", high, require_low_s=True)


def test_low_s_flag_on_sign(key):
    d, Q = key
    for k in range(1, N):
        try:
            sig = t.sign(d, "x", k=k, low_s=True)
        except ValueError:
            continue
        assert sig[1] <= N // 2 and t.verify(Q, "x", sig)


def test_random_nonce_signing(key):
    d, Q = key
    for _ in range(50):
        assert t.verify(Q, "random", t.sign(d, "random"))


def test_verify_rejects_out_of_range(key):
    d, Q = key
    r, s = t.sign(d, "m", k=13)
    for bad in ((0, s), (r, 0), (N, s), (r, N)):
        assert not t.verify(Q, "m", bad)
    assert not t.verify(None, "m", (r, s))


# ------------------------------------------------------------------ nonce reuse


@pytest.mark.parametrize("flip1,flip2", list(itertools.product([False, True], repeat=2)))
def test_nonce_reuse_recovers_key_all_low_s_flips(key, flip1, flip2):
    d, Q = key
    m1, m2, k = "pay alice 5", "pay bob 9", 13
    z1, z2 = t.hash_to_int(m1), t.hash_to_int(m2)
    s1, s2 = t.sign_hash(d, z1, k), t.sign_hash(d, z2, k)
    if flip1:
        s1 = (s1[0], N - s1[1])
    if flip2:
        s2 = (s2[0], N - s2[1])
    assert t.verify_hash(Q, z1, s1) and t.verify_hash(Q, z2, s2)
    rec_d, rec_k = t.recover_from_nonce_reuse(Q, z1, s1, z2, s2)
    assert rec_d == d
    assert rec_k in (k, N - k)


def test_nonce_reuse_exhaustive():
    """Every key, many nonces, all four flips: always the original d."""
    z1, z2 = 17, 50
    for d in range(1, N, 7):
        Q = t.scalar_mult(d, G)
        for k in range(1, N, 5):
            try:
                a, b = t.sign_hash(d, z1, k), t.sign_hash(d, z2, k)
            except ValueError:
                continue
            for f1, f2 in itertools.product([False, True], repeat=2):
                aa = (a[0], N - a[1]) if f1 else a
                bb = (b[0], N - b[1]) if f2 else b
                assert t.recover_from_nonce_reuse(Q, z1, aa, z2, bb)[0] == d


def test_normalized_pair_still_leaks(key):
    d, Q = key
    z1, z2 = 17, 50
    a = t.sign_hash(d, z1, 13, low_s=True)
    b = t.sign_hash(d, z2, 13, low_s=True)
    assert t.recover_from_nonce_reuse(Q, z1, a, z2, b)[0] == d


def test_different_nonces_rejected(key):
    d, Q = key
    a, b = t.sign_hash(d, 17, 13), t.sign_hash(d, 50, 14)
    assert a[0] != b[0]
    with pytest.raises(ValueError):
        t.recover_from_nonce_reuse(Q, 17, a, 50, b)
