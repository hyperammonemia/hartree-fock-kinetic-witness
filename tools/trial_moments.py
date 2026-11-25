"""Exact tensor-Gaussian moment check for the second and fourth excitations."""
from fractions import Fraction as F
from math import factorial, prod

# t is the squared longitudinal component of the standard Gaussian
# centre coordinate. v is its squared transverse radius. q=|x-y|².
trial2 = {(1,0,0): 1, (0,1,0): 1, (0,0,1): -1}
trial4 = {(0,0,2): 7, (2,0,0): -1, (1,1,0): -2, (0,2,0): -1,
          (1,0,1): -6, (0,1,1): -2, (1,0,0): 20, (0,1,0): 20,
          (0,0,1): -60, (0,0,0): 60}
states = [{(0,0,0): 1}, trial2, trial4]


def moment(x, y, coulomb):
    out = 0
    for (a,b,c), f in x.items():
        for (u,v,w), g in y.items():
            i,j,k = a+u,b+v,c+w
            radial = 2**k*factorial(k) if coulomb else prod(range(1,2*k+2,2))
            out += f*g*prod(range(1,2*i,2))*2**j*factorial(j)*radial
    return out


gram = [[moment(u,v,False) for v in states] for u in states]
kernel = [[moment(u,v,True) for v in states] for u in states]
assert gram == [[1,0,0],[0,12,0],[0,0,6720]]
assert kernel == [[1,1,21],[1,11,97],[21,97,4985]]
print("L2 Gram matrix", gram)
print("W matrix in units D=sqrt(2/pi)", kernel)
a, c = F(1,30), F(1,1600)
norm = 12*a*a+6720*c*c
cost = 24*a*a+26880*c*c
coupling = a*kernel[0][1]+c*kernel[0][2]
pair = a*a*kernel[1][1]+2*a*c*kernel[1][2]+c*c*kernel[2][2]
print("trial norm, oscillator, reference W, excited W", norm,cost,coupling,pair)

assert (norm, cost, coupling, pair) == (
    F(383, 24000), F(223, 6000), F(223, 4800), F(83917, 4608000)
)
lam = F(1, 100)
direct_lower = F(159, 200)
assert direct_lower**2 < F(7, 11)
assert F(2, 3) - F(7, 11) == F(1, 33)
upper = (cost - 2*coupling*direct_lower + lam*(pair + norm)) / (1 + lam**2*norm)
lower = -F(50, 49*33)
assert upper < -F(9, 250)
assert lower + F(9, 250) > F(1, 200)
print("scaled two-electron upper, one-electron lower, removal margin", upper, lower, lower-upper)
