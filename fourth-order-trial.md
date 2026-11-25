# Removal energy from the ordinary oscillator gap

Section 3 of the original construction uses the radial one-electron oscillator gap 2. A quartic two-electron trial gives the same strict removal margin using the ordinary Cartesian gap 1. The one-electron argument applies to all form-domain states and requires no one-electron ground eigenvector. The Gaussian spatial orbital, coupling and reference Hamiltonian are those of [the construction](continuum-witness.md).

## Two double excitations

Put $Y=\sqrt{2}\,x,\ V=\sqrt{2}\,y,\ S=(Y+V)/\sqrt{2}$, and $Z=(Y-V)/\sqrt{2}=x-y$. Under the squared reference Gaussian $D_0^2$, the vectors $S,Z$ are independent standard three-dimensional Gaussians, as are $Y,V$. Let $K(w)=|w|^4-10|w|^2+15$ and set
$$
 P_2=|S|^2-|Z|^2,\qquad P_4=8K(Z)-2K(Y)-2K(V).
$$
The ground-transformed oscillator acts as $-\Delta+w\cdot\nabla$ on each standard Gaussian variable. Applying it to these polynomials gives eigenvalues 2 and 4 respectively. In particular $(-\Delta+w\cdot\nabla)K=4K$. Both polynomials have zero conditional mean given either electron. Indeed $P_2=2Y\cdot V$, and at fixed $Y$ the moments of $|Y-V|^2$ and $|Y-V|^4$ are $|Y|^2+3$ and $|Y|^4+10|Y|^2+15$. Hence the conditional mean of $K(Z)$ is $K(Y)/4$. These identities make the reference-to-excitation matrix elements of **both** one-body Hartree potentials vanish.

## Exact matrices

In the ordered basis $(1,P_2,P_4)D_0$, the Gram matrix, the shifted oscillator matrix and the Coulomb matrix for $W=1/|x-y|$ are
$$
 G=\operatorname{diag}(1,12,6720),\quad H_0=\operatorname{diag}(0,24,26880),
 \quad W=D\begin{pmatrix}1&1&21\\1&11&97\\21&97&4985\end{pmatrix},
 \qquad D=\sqrt{2/\pi}.
$$
For a reproducible computation, condition on $Z$, take $t$ as the squared component of $S$ along $Z$, $v$ as its squared transverse radius, and $q=|Z|^2$. The event $Z=0$ has measure zero. Their moments factor. The first two factors are $(2i-1)!!$ and $2^j j!$ for powers $t^i,v^j$. The ordinary radial factor is $(2k+1)!!$ for $q^k$, and the $W$-weighted factor is $D\,2^k k!$. These follow by elementary Gaussian integration. In these variables $P_2=t+v-q$ and
$$
 P_4=7q^2-(t+v)^2-6tq-2vq+20(t+v)-60q+60.
$$

## Variational comparison

Use $U=(1-\lambda L)D_0$ with $L=P_2/30+P_4/1600$ and $\lambda=1/100$. The matrices give
$$
 N=\|LD_0\|^2=383/24000,\quad
 A=\langle LD_0,H_0 LD_0\rangle=223/6000,\quad
 B=\langle D_0,WLD_0\rangle/D=223/4800,\quad
 C=\langle LD_0,WLD_0\rangle/D=83917/4608000.
$$
The excited diagonal contribution of $-J_1-J_2$ is nonpositive. Since the reference energy is $-\lambda D$, the Rayleigh quotient yields
$$
 (1+\lambda^2 N)\frac{E_2+\lambda D}{\lambda^2}
 \le A-2DB+\lambda D(C+N).
$$
The bounds $159/200<D<1$ imply $(E_2+\lambda D)/\lambda^2<-9/250$.

For any normalized one-electron trial, decompose it along the Gaussian and its orthogonal complement. Write $a$ for the modulus of the Gaussian coefficient, $z$ for the norm of the complement divided by $\lambda$, and $\sigma^2=2/3-D^2$. On the complement the ordinary oscillator gap is 1. The shifted potential $\lambda(D-J)$ is bounded below by $-2\lambda$, and the off-diagonal matrix element of $J$ is bounded by $\sigma$ times the complementary norm. Consequently the shifted one-electron energy in units of $\lambda^2$ is bounded below by
$$
 \tfrac{49}{50}z^2-2\sigma a z \ \ge\ -\tfrac{50}{49}\sigma^2 \ \ge\ -\tfrac{50}{49\cdot33}.
$$
Here $a^2\le1$ and $\pi<22/7$ gives $\sigma^2<1/33$. This uniform bound passes to the infimum. Thus
$$
 (E_1-E_2)/\lambda^2 > 9/250-50/(49\cdot33)>1/200.
$$
Only the two-electron upper bound uses a polynomial trial. The calculation leaves $E_1$ and $E_2$ as the continuum variational energies.

Two standard-library Python programs check the matrices with exact arithmetic. The second starts in six Cartesian coordinates, differentiates the oscillator polynomials, checks both vanishing conditional means and then evaluates the Coulomb matrix by angular integration. Identifying the Gaussian measures and their moments with the physical energy form, and proving the ordinary oscillator bound on its full domain, remain steps in the Lean formalization. [Radial calculation](tools/trial_moments.py) · [Independent Cartesian calculation](tools/cartesian_trial.py)
