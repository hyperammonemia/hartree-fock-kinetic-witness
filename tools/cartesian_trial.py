"""Recompute the Gaussian trial directly in six Cartesian coordinates."""
from collections import Counter
from fractions import Fraction as F
from math import factorial, prod


ZERO = (0,) * 6


def term(e):
    return {e: 1}


def scale(p, a):
    return {e: a*c for e,c in p.items() if a*c}


def add(*terms):
    out = Counter()
    for p in terms:
        out.update(p)
    return {e:c for e,c in out.items() if c}


def mul(p,q):
    terms = Counter()
    for e,a in p.items():
        for f,b in q.items():
            terms[tuple(x+y for x,y in zip(e,f))] += a*b
    return {e:c for e,c in terms.items() if c}


def square(p):
    return mul(p,p)


def dot(p,q):
    return add(*(mul(x,y) for x,y in zip(p,q)))


def K(radius_sq):
    return add(square(radius_sq),scale(radius_sq,-10),scale(term(ZERO),15))


def trial(particle_coordinates):
    basis = [term(tuple(int(i==j) for j in range(6))) for i in range(6)]
    left,right = basis[:3],basis[3:]
    l,r,lr = dot(left,left),dot(right,right),dot(left,right)
    plus = scale(add(l,r,scale(lr,2)),F(1,2))
    minus = scale(add(l,r,scale(lr,-2)),F(1,2))
    if particle_coordinates:
        s,z,y,v = plus,minus,l,r
    else:
        s,z,y,v = l,r,plus,minus
    return term(ZERO),add(s,scale(z,-1)),add(scale(K(z),8),scale(K(y),-2),scale(K(v),-2))


def oscillator(p):
    out = scale(p,0)
    for e,c in p.items():
        out = add(out,{e:sum(e)*c})
        for i,n in enumerate(e):
            if n >= 2:
                f = list(e)
                f[i] -= 2
                out = add(out,{tuple(f):-n*(n-1)*c})
    return out


def gaussian(power):
    return 0 if power%2 else prod(range(1,power,2))


def conditional(p, start):
    out = Counter()
    for e,c in p.items():
        fixed = e[:3] if start==3 else e[3:]
        out[fixed] += c*prod(gaussian(n) for n in e[start:start+3])
    return {e:c for e,c in out.items() if c}


def integrate(p, coulomb):
    total = F()
    for e,c in p.items():
        value = c*prod(gaussian(n) for n in e)
        if not value:
            continue
        if coulomb:
            k = sum(e[3:])//2
            value *= F(2**k*factorial(k),prod(range(1,2*k+2,2)))
        total += value
    return total


def check():
    orbitals = trial(True)
    for p,n in zip(orbitals,[0,2,4]):
        assert oscillator(p) == scale(p,n)
        if n:
            assert conditional(p,0) == conditional(p,3) == {}
    relative = trial(False)
    gram = [[integrate(mul(f,g),False) for g in relative] for f in relative]
    pair = [[integrate(mul(f,g),True) for g in relative] for f in relative]
    assert gram == [[1,0,0],[0,12,0],[0,0,6720]]
    assert pair == [[1,1,21],[1,11,97],[21,97,4985]]
    print("The Cartesian oscillator identities, both conditional means and both matrices agree.")


if __name__ == "__main__":
    check()
