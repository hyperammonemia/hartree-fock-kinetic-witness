# An exterior density bound from the squared marginal

This proof uses the radial density that the kinetic-energy probe actually integrates. It applies even when the reference two-electron spatial state has angular dependence. The exact state belongs to the real or complex scalar form domain $Q=H^1(\mathbb R^6)\cap L^2((|x|^2+|y|^2)\,dx\,dy)$, has norm one and satisfies the full weak eigenvalue equation at energy $E_2$. Write $E_1$ for any lower bound of the full one-electron form $h_0-\lambda J$. The difference $d=E_1-E_2>5\cdot10^{-7}$ suffices.

## The radial quantities and their derivatives

Use surface probability measure $d\sigma=d\omega/(4\pi)$ on the unit sphere. For almost every $r>0$, define
$$
 a(r)=\int_{S^2}\!\int_{\mathbb R^3}|\Psi(r\omega,y)|^2\,dy\,d\sigma,
 \qquad u(r)=\pi^{-3/4}e^{-r^2/2},\quad
 M(r)=a(r)/u(r)^2,\quad p(r)=r^2 e^{-r^2}.
$$
On each compact interval away from zero, $a$ has an absolutely continuous representative with
$$
 a'(r)=2\operatorname{Re}\int_{S^2}\!\int
     \overline{\Psi(r\omega,y)}\,\omega\cdot\nabla_x\Psi(r\omega,y)\,dy\,d\sigma
 \quad\text{almost everywhere}.
$$
Indeed, smooth approximations in $H^1$ converge on such annuli in the radial–angular $L^2$ norm, including their radial derivatives. Products for the displayed identity converge in $L^1$ by Cauchy–Schwarz. Testing with scalar smooth functions of $r$ identifies the distributional derivative. This also gives $M\in W^{1,1}_{\rm loc}(0,\infty)$.

The integral $4\pi\int r^2 a(r)\,dr$ equals one. Thus $a(q)\le1$ for some $q\in[100000,100001]$. The identity
$$
 pM'=\pi^{3/2}r^2(a'+2ra)
$$
gives $pM'\in L^1(q,\infty)$. In its first term use Cauchy–Schwarz on the full product measure to bound the integral of $|\Psi||\nabla_x\Psi|$. The second term is bounded by the product of $\|\Psi\|_2$ and $\||x|\Psi\|_2$. This flux estimate allows the transformed density $M$ itself to be large.

## Test the actual eigenvalue equation with a scalar multiplier

Take a nonnegative Lipschitz $h$ compactly supported in $(q,\infty)$. The test $h(|x|)\Psi$ belongs to $Q$ by the ordinary weak product rule with a bounded Lipschitz multiplier. The spatial two-electron ground eigenfunction satisfies its weak equation on the full scalar domain, so this test may depend on just one electron.

Transform the $x$-oscillator form by its positive Gaussian ground state. Put $Z=\Psi/u(|x|)$. In the support of the test the identity for this form is
$$
 \frac12\int u^2 h\,|\nabla_x Z|^2\,dx\,dy
 +\frac14\int u^2 h'(|x|)\,\partial_r |Z|^2\,dx\,dy .
$$
It follows by integration by parts, first for smooth states and then by local $H^1$ approximation. On the compact annulus the multipliers $u,1/u$ and their first derivatives are bounded. The first term is nonnegative. In the second term, angular and $y$ integration of $\partial_r|Z|^2$ gives $M'$. Each $y$-fiber of the residual one-body form has lower bound $E_1\|\Psi(x,\cdot)\|_2^2$, and the Coulomb repulsion contributes a nonnegative term. With $V(r)=d-\lambda J(r)$, division by the common positive constant $4\pi\pi^{-3/2}$ gives the following inequality for every such test:
$$
 \int_q^\infty \left[\tfrac14p M' h'+pVMh\right]dr\le0.
$$
The sign only uses the residual Rayleigh lower bound and repulsiveness. The one-electron infimum may be taken over all complex states. For a real external potential each form and norm split additively into real and imaginary components.

## The explicit density barrier

Set $\alpha=10^{-7}$ and $B(r)=u(q)^{-2}(q/r)^{2\alpha}$. Then $M(q)\le B(q)$. Write $\mathcal L B= -(pB')'/(4p)+VB$. Direct differentiation gives
$$
 \mathcal L B/B=-\alpha+\frac{\alpha(1-2\alpha)}{2r^2}+d-\lambda J(r)>0
 \quad(r\ge q).
$$
Here $p'/p=2/r-2r$, $B'/B=-2\alpha/r$, and $0\le\lambda J(r)\le 10^{-7}$. The coefficient $V$ is strictly positive. Gaussian decay ensures $pB'\in L^1(q,\infty)$. On subtracting the barrier inequality obtained by ordinary integration by parts, the locally absolutely continuous function $v=M-B$ and its integrable flux $F=pv'$ satisfy
$$
 v(q)\le0,\qquad \int_q^\infty [Fh'+4pVvh]dr\le0.
$$

## Compact test functions prove comparison

Suppose $v(c)>0$. Its open positive component containing $c$ is an interval $(a,b)$ with $a\ge q$. Continuity gives $v(a)=0$, including when $a=q$. Choose $l\in(a,c)$ with $v(l)<v(c)$, and set $I_{ij}=\int_i^j p^{-1}dr>0$ for compact subintervals of the exterior.

On $[l,c]$ let the test rise from zero to one by setting $h(r)=I_{lr}/I_{lc}$. Its ascending contribution to $\int Fh'$ is exactly
$$
 A=\frac{1}{I_{lc}}\int_l^c F/p\,dr
   =\frac{v(c)-v(l)}{I_{lc}}>0 .
$$
If $b<\infty$, choose $t\in(c,b)$ so that $v(t)<v(c)$, using $v(b)=0$. On $[c,t]$ set $h(r)=I_{rt}/I_{ct}$, with value zero outside $[l,t]$. The descending contribution is $(v(c)-v(t))/I_{ct}>0$. The test is nonnegative and supported where $v>0$, hence the potential integral is nonnegative. The weak inequality is contradicted.

If $b=\infty$, extend the ascending test by one from $c$ to $S$, then put $h(r)=S+1-r$ on $[S,S+1]$ and zero to its right. Its descending contribution has absolute value at most $\int_S^{S+1}|F|$, which tends to zero by global flux integrability. Choose finite $S>c$ with this bound below $A$. The total derivative contribution is again positive, and the potential term stays nonnegative. This exhausts the possible positive components.

Every test just used is a fixed compactly supported Lipschitz function of radius, with piecewise continuous bounded derivative. If smooth tests are preferred, convolution with nonnegative compactly supported mollifiers keeps their supports inside the positive component for sufficiently small radii. The derivatives converge away from the finitely many joins and are uniformly bounded at each fixed choice of endpoints. Since $F\in L^1$ the limits in the weak form follow by dominated convergence.

It follows that $M(r)\le B(r)$ for every $r\ge q$. Taking nonnegative square roots yields
$$
 \sqrt{a(r)}\le u(r)\,u(q)^{-1}(q/r)^\alpha.
$$
The previously checked exponential estimate gives $\sqrt{a(r)}<u(r)/2$ for $r\ge\exp(10^{18})$. The radial kinetic probe integrates this spherical average against its nonnegative radial weight, so precisely this estimate supplies the required tail deficit.
