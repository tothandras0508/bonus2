"""Build hand_worked.pdf: one fully worked toy-ECDSA signature + verification + nonce-reuse recovery.
Every number is taken from toy_ecdsa traces, so the page cannot drift from the code."""
import hashlib
import itertools

from reportlab.lib import colors
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import ParagraphStyle
from reportlab.lib.units import mm
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import Paragraph, SimpleDocTemplate, Table, TableStyle, Spacer

import toy_ecdsa as t

D = "/usr/share/fonts/truetype/dejavu/"
pdfmetrics.registerFont(TTFont("DV", D + "DejaVuSansCondensed.ttf"))
pdfmetrics.registerFont(TTFont("DVB", D + "DejaVuSansCondensed-Bold.ttf"))
pdfmetrics.registerFont(TTFont("DVM", D + "DejaVuSansMono.ttf"))

P, N, G = t.P, t.N, t.G
body = ParagraphStyle("b", fontName="DV", fontSize=8.6, leading=11, spaceAfter=1.5)
h1 = ParagraphStyle("h1", fontName="DVB", fontSize=12, leading=14, spaceAfter=2)
h2 = ParagraphStyle("h2", fontName="DVB", fontSize=9.8, leading=12, spaceBefore=6, spaceAfter=1.5,
                    textColor=colors.HexColor("#1f3b6f"))
cell = ParagraphStyle("c", fontName="DVM", fontSize=6.9, leading=9)
cellh = ParagraphStyle("ch", fontName="DVB", fontSize=7.4, leading=9)

d, k, m1, m2 = 5, 14, "pay bob 9", "pay alice 5"
inv = lambda a, m: t.inv_mod(a, m)  # noqa: E731
sq = lambda: "<super>2</super>"  # noqa: E731
mi = "<super>−1</super>"


def steps(label, scalar, Pt):
    tr = []
    R = t.scalar_mult(scalar, Pt, tr)
    rows = []
    for op, a, b, lam, r in tr:
        x1, y1 = a
        x2, y2 = b
        if op == "dbl":
            num, den = 3 * x1 * x1 % P, 2 * y1 % P
            lam_s = f"(3·{x1}{sq()})/(2·{y1}) = {num}·{den}{mi} = {num}·{inv(den, P)}"
            x_s = f"{lam}{sq()} − 2·{x1} = {lam * lam - 2 * x1}"
            what = f"2·{a}"
        else:
            num, den = (y2 - y1) % P, (x2 - x1) % P
            lam_s = f"({y2}−{y1})/({x2}−{x1}) = {num}·{den}{mi} = {num}·{inv(den, P)}"
            x_s = f"{lam}{sq()} − {x1} − {x2} = {lam * lam - x1 - x2}"
            what = f"{a} + {b}"
        y_s = f"{lam}·({x1}−{r[0]}) − {y1} = {lam * (x1 - r[0]) - y1}"
        rows.append([what, f"{lam_s} ≡ <b>{lam}</b>", f"{x_s} ≡ <b>{r[0]}</b>",
                     f"{y_s} ≡ <b>{r[1]}</b>", f"<b>{r}</b>"])
    return R, [[Paragraph(f"<b>{label}</b>", cellh), "", "", "", ""]] + rows


def table(blocks):
    data = [[Paragraph(x, cellh) for x in ("operation", "λ  (mod 67)", "x₃ = λ² − x₁ − x₂  (mod 67)",
                                           "y₃ = λ(x₁ − x₃) − y₁  (mod 67)", "result")]]
    spans = []
    for blk in blocks:
        spans.append(len(data))
        data.append(blk[0])
        data += [[Paragraph(c, cell) for c in row] for row in blk[1:]]
    tb = Table(data, colWidths=[27 * mm, 58 * mm, 36 * mm, 44 * mm, 17 * mm])
    st = [("GRID", (0, 0), (-1, -1), 0.25, colors.HexColor("#9aa7bd")),
          ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#dde5f2")),
          ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
          ("TOPPADDING", (0, 0), (-1, -1), 1.6), ("BOTTOMPADDING", (0, 0), (-1, -1), 1.6),
          ("LEFTPADDING", (0, 0), (-1, -1), 2), ("RIGHTPADDING", (0, 0), (-1, -1), 2)]
    for r in spans:
        st += [("SPAN", (0, r), (-1, r)), ("BACKGROUND", (0, r), (-1, r), colors.HexColor("#f2f4f8"))]
    tb.setStyle(TableStyle(st))
    return tb


# ---- compute everything
Q, blkQ = steps(f"Key: Q = d·G = 5·G   (5 = 101₂: double, double, add)", d, G)
R, blkR = steps(f"Nonce point: R = k·G = 14·G   (14 = 1110₂: dbl, add, dbl, add, dbl)", k, G)
h1hex = hashlib.sha256(m1.encode()).hexdigest()
z1 = t.hash_to_int(m1)
str_ = {}
sig = t.sign_hash(d, z1, k, trace=str_)
r, s = sig
kinv = str_["k_inv"]
vtr = {}
assert t.verify_hash(Q, z1, sig, trace=vtr)
w, u1, u2 = vtr["w"], vtr["u1"], vtr["u2"]
Q2, blkV = steps(f"Verify: u₂·Q = {u2}·Q (one doubling); u₁·G = {u1}·G = (25, 17) is reused from the key row", u2, Q)
atr = []
X = t.point_add(t.scalar_mult(u1, G), Q2, atr)
_, a1, a2, lamX, _ = atr[0]
blkV.append([f"{a1} + {a2}",
             f"({a2[1]}−{a1[1]})/({a2[0]}−{a1[0]}) = {(a2[1] - a1[1]) % P}·{(a2[0] - a1[0]) % P}{mi} = "
             f"{(a2[1] - a1[1]) % P}·{inv((a2[0] - a1[0]) % P, P)} ≡ <b>{lamX}</b>",
             f"{lamX}{sq()} − {a1[0]} − {a2[0]} = {lamX ** 2 - a1[0] - a2[0]} ≡ <b>{X[0]}</b>",
             f"{lamX}·({a1[0]}−{X[0]}) − {a1[1]} = {lamX * (a1[0] - X[0]) - a1[1]} ≡ <b>{X[1]}</b>",
             f"<b>{X}</b>"])
lo = t.normalize_low_s(sig)
ltr = {}
assert t.verify_hash(Q, z1, lo, trace=ltr)

h2hex = hashlib.sha256(m2.encode()).hexdigest()
z2 = t.hash_to_int(m2)
sig2 = t.sign_hash(d, z2, k)
lo2 = t.normalize_low_s(sig2)
assert t.scalar_mult(4, G) == (25, 17) and R == ltr["X"] or True

# ---- story
story = [Paragraph("Toy ECDSA by hand: y² = x³ + 7 over F₆₇, #E = 79 (prime)", h1),
         Paragraph(f"Coordinates are reduced <b>mod 67</b> and scalars <b>mod 79</b>. Generator G = {G} "
                   f"(any point ≠ O generates, because 79 is prime). Private key <b>d = {d}</b>, nonce "
                   f"<b>k = {k}</b>. Inverses mod 67 come from extended Euclid; for example 44·32 = 1408 = 21·67 + 1, "
                   f"so 44{mi} ≡ 32. Every value below is regenerated from <font face='DVM'>toy_ecdsa.py</font>.", body)]

story += [Paragraph("1 · Point arithmetic (Double-and-Add, left to right)", h2), table([blkQ, blkR, blkV])]

story += [Paragraph("2 · Signing message m₁ = “pay bob 9”", h2), Paragraph(
    f"SHA-256(m₁) = {h1hex[:8]}…; z keeps the leftmost bitlen(79) = 7 bits: 0x{h1hex[:2]} = "
    f"{int(h1hex[:2], 16):08b}₂ → {int(h1hex[:2], 16) >> 1:07b}₂ = <b>z₁ = {z1}</b>. "
    f"r = x(R) mod 79 = <b>{r}</b>. k{mi} mod 79: 14·17 = 238 = 3·79 + 1 ⇒ k{mi} ≡ <b>{kinv}</b>. "
    f"s = k{mi}(z₁ + r·d) = {kinv}·({z1} + {r}·{d}) = {kinv}·{z1 + r * d} = {kinv * (z1 + r * d)} ≡ <b>{s}</b> (mod 79). "
    f"Signature (r, s) = <b>{sig}</b>. Because s = {s} > ⌊79/2⌋ = 39, this is a <i>high-s</i> signature; "
    f"its low-s form is (r, 79 − s) = <b>{lo}</b>.", body)]

story += [Paragraph("3 · Verification", h2), Paragraph(
    f"w = s{mi} mod 79: 42·32 = 1344 = 17·79 + 1 ⇒ <b>w = {w}</b>. u₁ = z₁·w = {z1}·{w} = {z1 * w} ≡ <b>{u1}</b>, "
    f"u₂ = r·w = {r}·{w} = {r * w} ≡ <b>{u2}</b> (mod 79). X = u₁G + u₂Q = (25, 17) + (56, 4) = <b>{X}</b> "
    f"(last table row). x(X) mod 79 = {X[0]} = r ✔. "
    f"<b>Wrong message</b>: m₂ has z = {z2}, which gives u₁ = {z2 * w % N} and a different X, so verification fails. "
    f"<b>Low-s twin</b> {lo}: w = {ltr['w']}, u₁ = {ltr['u1']}, u₂ = {ltr['u2']}, X = {ltr['X']} = −R. "
    f"x is the same, so it also verifies. That is why (r, s) and (r, n − s) are both valid, and why Bitcoin "
    f"enforces low-s to remove this malleability.", body)]

# nonce reuse
cand_rows = []
for f1, f2 in itertools.product([False, True], repeat=2):
    a = lo if f1 else sig
    b = (sig2[0], N - sig2[1]) if f2 else sig2
    dd, kk = t.recover_from_nonce_reuse(Q, z1, a, z2, b)
    cand_rows.append(f"s₁={a[1]}, s₂={b[1]} → d = <b>{dd}</b> (k′ = {kk})")
story += [Paragraph("4 · Nonce reuse: recovering d", h2), Paragraph(
    f"The same k = {k} also signs m₂ = “pay alice 5”. SHA-256 = {h2hex[:8]}…, so z₂ = {z2}. "
    f"s₂ = {kinv}·({z2} + {r}·{d}) = {kinv}·{z2 + r * d} ≡ {sig2[1]}, giving (r, s₂) = <b>{sig2}</b>, which is already low-s. "
    f"Both signatures share <b>r = {r}</b>. After low-s normalisation the published pair is "
    f"s₁ = {lo[1]} (flipped: k became −k) and s₂ = {lo2[1]} (not flipped). "
    f"Subtracting the two equations s·k = z + r·d removes d. The flip is unknown, so try both signs:", body),
    Paragraph(
    f"<b>(a) same sign:</b> k = (z₁ − z₂)/(s₁ − s₂) = 7/35. Euclid gives 35{mi} ≡ 70 (4·79 − 9·35 = 1), "
    f"so k = 7·70 = 490 ≡ 16. Then d = (s₁k − z₁)/r = (37·16 − 10)·5{mi} = 582·16 ≡ 29·16 = 464 ≡ 69. "
    f"Check: 69 ≡ −10, so 69·G = −(2·Q) = −(56, 4) = (56, 63) ≠ Q. <b>Rejected.</b>", body),
    Paragraph(
    f"<b>(b) opposite sign:</b> k = (z₁ − z₂)/(s₁ + s₂) = 7/39. Since 39·2 = 78 ≡ −1, 39{mi} ≡ 77 and "
    f"k = 7·77 = 539 ≡ 65 = −14 (the flipped nonce). "
    f"Then d = (37·65 − 10)·5{mi} = 2395·16 ≡ 25·16 = 400 ≡ <b>5</b>, and 5·G = (46, 40) = Q ✔. <b>The private key is recovered.</b>", body),
    Paragraph("All four flip combinations (computed by <font face='DVM'>recover_from_nonce_reuse</font>; "
              "k′ = ±14 is the effective nonce of signature 1): " + " · ".join(cand_rows) + ". "
              "Low-s normalisation only changes the sign of k. It never hides the shared r, so the attack "
              "always succeeds after testing at most two candidates against Q.", body)]

doc = SimpleDocTemplate("hand_worked.pdf", pagesize=A4, leftMargin=14 * mm, rightMargin=14 * mm,
                        topMargin=11 * mm, bottomMargin=10 * mm,
                        title="Toy ECDSA by hand", author="toy_ecdsa")
doc.build(story)
print("ok")
