"""Emitted by emit_lean.py from wlib.py: the correction and quadratic blocks as plain
Python, for validation against honest 6 x 6 collection.  Do not edit by hand."""


def gaTwoCorrM(s, x, y, z0, z1, z2):
    return (z0.f * (-s.c * x.d + s.d * x.c - 4 * x.c * x.d + 2 * x.c * y.d + y.c * y.d)
        + z0.g * (8 * x.a * x.d - 2 * x.a * y.d - 2 * x.d * y.a - 2 * y.a * y.d)
        + z0.h * (s.a * x.b - s.b * x.a - 4 * x.a * x.b + 2 * x.b * y.a + y.a * y.b)
        + z1.f * (3 * s.c * x.d - 2 * s.c * y.d + s.d * x.c - 20 * x.c * x.d + 20 * x.c * y.d
            - 4 * y.c * y.d)
        + z1.g * (2 * s.a * s.d - 14 * s.a * x.d + 10 * s.a * y.d - 14 * s.d * x.a + 10 * s.d * y.a
            + 130 * x.a * x.d - 100 * x.a * y.d - 100 * x.d * y.a + 80 * y.a * y.d)
        + z1.h * (-2 * s.a * s.b + 11 * s.a * x.b - 8 * s.a * y.b + 13 * s.b * x.a - 10 * s.b * y.a
            - 110 * x.a * x.b + 80 * x.a * y.b + 100 * x.b * y.a - 76 * y.a * y.b)
        + z2.f * (-2 * s.c * y.d + s.d * y.c)
        + z2.g * (s.a * y.d + s.d * y.a)
        + z2.h * (s.a * y.b - 2 * s.b * y.a))


def gaTwoCorrN(s, x, y, z0, z1, z2):
    return (z0.g * (-s.d * x.e + s.e * x.d - 4 * x.d * x.e + 2 * x.d * y.e + y.d * y.e)
        + z0.h * (8 * x.b * x.e - 2 * x.b * y.e - 2 * x.e * y.b - 2 * y.b * y.e)
        + z0.i * (s.b * x.c - s.c * x.b - 4 * x.b * x.c + 2 * x.c * y.b + y.b * y.c)
        + z1.g * (3 * s.d * x.e - 2 * s.d * y.e + s.e * x.d - 20 * x.d * x.e + 20 * x.d * y.e
            - 4 * y.d * y.e)
        + z1.h * (2 * s.b * s.e - 14 * s.b * x.e + 10 * s.b * y.e - 14 * s.e * x.b + 10 * s.e * y.b
            + 130 * x.b * x.e - 100 * x.b * y.e - 100 * x.e * y.b + 80 * y.b * y.e)
        + z1.i * (-2 * s.b * s.c + 11 * s.b * x.c - 8 * s.b * y.c + 13 * s.c * x.b - 10 * s.c * y.b
            - 110 * x.b * x.c + 80 * x.b * y.c + 100 * x.c * y.b - 76 * y.b * y.c)
        + z2.g * (-2 * s.d * y.e + s.e * y.d)
        + z2.h * (s.b * y.e + s.e * y.b)
        + z2.i * (s.b * y.c - 2 * s.c * y.b))


def gaTwoCorrO(s, x, y, z0, z1, z2):
    return (z0.f * (-s.c * x.i + s.e * x.h - s.h * x.e + s.i * x.c - 4 * x.c * x.i + 2 * x.c * y.i
            - 4 * x.e * x.h + 2 * x.h * y.e + y.c * y.i + y.e * y.h + s.c * s.d * x.e
            - s.c * s.e * x.d + 4 * s.c * x.d * x.e - 2 * s.c * x.d * y.e - s.c * y.d * y.e
            - 3 * s.d * x.c * x.e + 2 * s.d * x.c * y.e + s.d * y.c * y.e - s.e * x.c * x.d
            + 10 * x.c * x.d * x.e - 8 * x.c * x.d * y.e + x.c * y.d * y.e)
        + z0.g * (8 * x.a * x.i - 2 * x.a * y.i - 2 * x.i * y.a - 2 * y.a * y.i - 4 * s.d * x.a * x.e
            + 2 * s.d * x.e * y.a + s.d * y.a * y.e + 4 * s.e * x.a * x.d - 2 * s.e * x.d * y.a
            - s.e * y.a * y.d - 22 * x.a * x.d * x.e + 14 * x.a * x.d * y.e - x.a * y.d * y.e
            + 8 * x.d * x.e * y.a - 4 * x.d * y.a * y.e - 2 * y.a * y.d * y.e)
        + z0.h * (8 * x.e * x.f - 2 * x.e * y.f - 2 * x.f * y.e - 2 * y.e * y.f - 4 * s.a * x.b * x.e
            + 2 * s.a * x.b * y.e + s.a * y.b * y.e + 4 * s.b * x.a * x.e - 2 * s.b * x.a * y.e
            - s.b * y.a * y.e + 14 * x.a * x.b * x.e - 6 * x.a * x.b * y.e
            - 14 * x.b * x.e * y.a + 4 * x.b * y.a * y.e + 3 * x.e * y.a * y.b
            + 4 * y.a * y.b * y.e)
        + z0.i * (s.a * x.g - s.c * x.f + s.f * x.c - s.g * x.a - 4 * x.a * x.g - 4 * x.c * x.f
            + 2 * x.c * y.f + 2 * x.g * y.a + y.a * y.g + y.c * y.f - s.a * s.b * x.c
            + s.a * s.c * x.b + 3 * s.b * x.a * x.c - 2 * s.b * x.c * y.a - s.b * y.a * y.c
            - 3 * s.c * x.a * x.b + 2 * s.c * x.b * y.a + s.c * y.a * y.b - 2 * x.a * x.b * x.c
            + 6 * x.b * x.c * y.a - 3 * x.c * y.a * y.b - 2 * y.a * y.b * y.c)
        + z0.j * (-s.d * x.e + s.e * x.d - 4 * x.d * x.e + 2 * x.d * y.e + y.d * y.e)
        + z0.k * (8 * x.a * x.e - 2 * x.a * y.e - 2 * x.e * y.a - 2 * y.a * y.e)
        + z0.l * (s.a * x.b - s.b * x.a - 4 * x.a * x.b + 2 * x.b * y.a + y.a * y.b)
        + z1.f * (3 * s.c * x.i - 2 * s.c * y.i + s.e * x.h + 3 * s.h * x.e - 2 * s.h * y.e
            + s.i * x.c - 20 * x.c * x.i + 20 * x.c * y.i - 20 * x.e * x.h + 20 * x.h * y.e
            - 4 * y.c * y.i - 4 * y.e * y.h - 6 * s.c * x.d * x.e + 6 * s.c * x.d * y.e
            - 5 * s.c * y.d * y.e - 3 * s.d * x.c * x.e + 2 * s.d * x.c * y.e
            + 8 * s.d * y.c * y.e - s.e * x.c * x.d - 4 * s.e * y.c * y.d + 35 * x.c * x.d * x.e
            - 40 * x.c * x.d * y.e + 10 * x.c * y.d * y.e)
        + z1.g * (2 * s.a * s.i - 14 * s.a * x.i + 10 * s.a * y.i - 14 * s.i * x.a + 10 * s.i * y.a
            + 130 * x.a * x.i - 100 * x.a * y.i - 100 * x.i * y.a + 80 * y.a * y.i
            - 3 * s.a * s.d * x.e + 2 * s.a * s.d * y.e - s.a * s.e * x.d + 10 * s.a * x.d * x.e
            - 8 * s.a * x.d * y.e + s.a * y.d * y.e + 12 * s.d * x.a * x.e - 8 * s.d * x.a * y.e
            - 6 * s.d * x.e * y.a + 4 * s.d * y.a * y.e + 4 * s.e * x.a * x.d
            - 2 * s.e * x.d * y.a - 65 * x.a * x.d * x.e + 60 * x.a * x.d * y.e
            - 10 * x.a * y.d * y.e + 40 * x.d * x.e * y.a - 40 * x.d * y.a * y.e
            + 8 * y.a * y.d * y.e)
        + z1.h * (2 * s.e * s.f - 14 * s.e * x.f + 10 * s.e * y.f - 14 * s.f * x.e + 10 * s.f * y.e
            + 130 * x.e * x.f - 100 * x.e * y.f - 100 * x.f * y.e + 80 * y.e * y.f
            - 6 * s.a * s.b * x.e + 6 * s.a * s.b * y.e - 9 * s.a * s.e * x.b
            + 8 * s.a * s.e * y.b + 96 * s.a * x.b * x.e - 78 * s.a * x.b * y.e
            - 80 * s.a * x.e * y.b + 64 * s.a * y.b * y.e - 7 * s.b * s.e * x.a
            + 6 * s.b * s.e * y.a + 88 * s.b * x.a * x.e - 74 * s.b * x.a * y.e
            - 72 * s.b * x.e * y.a + 60 * s.b * y.a * y.e + 94 * s.e * x.a * x.b
            - 80 * s.e * x.a * y.b - 72 * s.e * x.b * y.a + 61 * s.e * y.a * y.b
            - 965 * x.a * x.b * x.e + 780 * x.a * x.b * y.e + 800 * x.a * x.e * y.b
            - 640 * x.a * y.b * y.e + 740 * x.b * x.e * y.a - 600 * x.b * y.a * y.e
            - 610 * x.e * y.a * y.b + 488 * y.a * y.b * y.e)
        + z1.i * (-2 * s.a * s.g + 11 * s.a * x.g - 8 * s.a * y.g - 2 * s.c * s.f + 13 * s.c * x.f
            - 10 * s.c * y.f + 11 * s.f * x.c - 8 * s.f * y.c + 13 * s.g * x.a - 10 * s.g * y.a
            - 110 * x.a * x.g + 80 * x.a * y.g - 110 * x.c * x.f + 100 * x.c * y.f
            + 80 * x.f * y.c + 100 * x.g * y.a - 76 * y.a * y.g - 76 * y.c * y.f
            + 9 * s.a * s.b * x.c - 8 * s.a * s.b * y.c + 10 * s.a * s.c * x.b
            - 8 * s.a * s.c * y.b - 100 * s.a * x.b * x.c + 80 * s.a * x.b * y.c
            + 80 * s.a * x.c * y.b - 60 * s.a * y.b * y.c + 7 * s.b * s.c * x.a
            - 6 * s.b * s.c * y.a - 97 * s.b * x.a * x.c + 80 * s.b * x.a * y.c
            + 78 * s.b * x.c * y.a - 72 * s.b * y.a * y.c - 97 * s.c * x.a * x.b
            + 80 * s.c * x.a * y.b + 74 * s.c * x.b * y.a - 57 * s.c * y.a * y.b
            + 995 * x.a * x.b * x.c - 800 * x.a * x.b * y.c - 800 * x.a * x.c * y.b
            + 640 * x.a * y.b * y.c - 780 * x.b * x.c * y.a + 640 * x.b * y.a * y.c
            + 610 * x.c * y.a * y.b - 496 * y.a * y.b * y.c)
        + z1.j * (3 * s.d * x.e - 2 * s.d * y.e + s.e * x.d - 20 * x.d * x.e + 20 * x.d * y.e
            - 4 * y.d * y.e)
        + z1.k * (2 * s.a * s.e - 14 * s.a * x.e + 10 * s.a * y.e - 14 * s.e * x.a + 10 * s.e * y.a
            + 130 * x.a * x.e - 100 * x.a * y.e - 100 * x.e * y.a + 80 * y.a * y.e)
        + z1.l * (-2 * s.a * s.b + 11 * s.a * x.b - 8 * s.a * y.b + 13 * s.b * x.a - 10 * s.b * y.a
            - 110 * x.a * x.b + 80 * x.a * y.b + 100 * x.b * y.a - 76 * y.a * y.b)
        + z2.f * (-2 * s.c * y.i + s.e * y.h - 2 * s.h * y.e + s.i * y.c + s.c * s.d * y.e
            - s.c * s.e * y.d)
        + z2.g * (s.a * y.i + s.i * y.a + s.a * s.d * y.e + 2 * s.d * y.a * y.e - s.e * y.a * y.d)
        + z2.h * (s.e * y.f + s.f * y.e - s.a * s.b * y.e + s.a * y.b * y.e - s.b * s.e * y.a
            - 2 * s.b * y.a * y.e - s.e * y.a * y.b)
        + z2.i * (s.a * y.g - 2 * s.c * y.f + s.f * y.c - 2 * s.g * y.a - s.a * s.b * y.c
            + s.a * s.c * y.b - s.a * y.b * y.c + s.b * s.c * y.a + 2 * s.c * y.a * y.b)
        + z2.j * (-2 * s.d * y.e + s.e * y.d)
        + z2.k * (s.a * y.e + s.e * y.a)
        + z2.l * (s.a * y.b - 2 * s.b * y.a))


def gaTwoQuadM(z0, z1, z2):
    return (z0.f * z1.h - z0.h * z1.f + 10 * z1.f * z1.h - 8 * z1.f * z2.h + z2.f * z2.h)


def gaTwoQuadN(z0, z1, z2):
    return (z0.g * z1.i - z0.i * z1.g + 10 * z1.g * z1.i - 8 * z1.g * z2.i + z2.g * z2.i)


def gaTwoQuadO(s, x, y, z0, z1, z2):
    return ((z0.f * z1.l - z0.i * z1.j + z0.j * z1.i - z0.l * z1.f + 10 * z1.f * z1.l
            - 8 * z1.f * z2.l + 10 * z1.i * z1.j - 8 * z1.j * z2.i + z2.f * z2.l + z2.i * z2.j)
        + s.a * (z0.i * z1.g - 4 * z1.g * z1.i + 2 * z1.g * z2.i + z2.g * z2.i)
        + s.c * (-z0.f * z1.i - z0.i * z1.f + 4 * z1.f * z1.i - 2 * z1.f * z2.i - 2 * z2.f * z2.i)
        + s.e * (z0.f * z1.h + z2.f * z2.h)
        + x.a * (7 * z0.g * z1.i - 2 * z0.g * z2.i - 4 * z0.i * z1.g + 30 * z1.g * z1.i
            - 20 * z1.g * z2.i)
        + x.c * (-3 * z0.f * z1.i + 2 * z0.f * z2.i + z0.i * z1.f - 20 * z1.f * z1.i
            + 20 * z1.f * z2.i)
        + x.e * (-4 * z0.f * z1.h + 3 * z0.h * z1.f - 10 * z1.f * z1.h)
        + y.a * (-2 * z0.g * z1.i - 2 * z0.g * z2.i + 2 * z0.i * z1.g + z0.i * z2.g
            - 20 * z1.g * z1.i + 16 * z1.g * z2.i - z2.g * z2.i)
        + y.c * (z0.f * z2.i + z0.i * z2.f + 8 * z1.f * z1.i - 12 * z1.f * z2.i)
        + y.e * (2 * z0.f * z1.h + z0.f * z2.h - 2 * z0.h * z1.f - 2 * z0.h * z2.f + 12 * z1.f * z1.h
            - 4 * z1.f * z2.h + z2.f * z2.h))
