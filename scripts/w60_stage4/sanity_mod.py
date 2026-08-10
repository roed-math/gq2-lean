"""W60-STAGE4 step 0b: the module route agrees with the honest closure at the wave-59 point."""
import sys
import os

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_force5"))

import u6mat as M                                             # noqa: E402
import modlib as MD                                           # noqa: E402
import gam3lib as G                                           # noqa: E402
import pointlib as P                                          # noqa: E402

sigma, X, Y, U, V = M.sigFiveMark, M.sepX, M.sepY, M.sepU, M.sepV
letters = [sigma, X, Y, U, V]

b3 = G.gamma3_module(letters)
b4 = G.gamma4_module(letters)
print("Howell:   |gamma_3(im)| = %d   |gamma_4(im)| = %d"
      % (MD.card(b3, 6), MD.card(b4, 6)))

g3, g4, g5 = P.gamma_series(letters)
print("closure:  |gamma_3(im)| = %d   |gamma_4(im)| = %d   |gamma_5(im)| = %d"
      % (len(g3), len(g4), len(g5)))

m3 = MD.members(b3, 6)
print("the two gamma_3 sets agree elementwise: %s" % (m3 == {G.vec(z) for z in g3}))
m4 = MD.members(b4, 6)
print("the two gamma_4 sets agree elementwise: %s" % (m4 == {G.vec(z) for z in g4}))

sh = G.ga4_shaped_elements(b3)
hon = {(z[12], z[13], z[14]) for z in P.gaFour_shaped(g3)}
print("gamma_4-shaped part of gamma_3(im): Howell %d, honest %d, equal %s"
      % (len(sh), len(hon), sh == hon))
print("its (m, n) parity classes: %s" % sorted(G.mn_parities(b3)))
