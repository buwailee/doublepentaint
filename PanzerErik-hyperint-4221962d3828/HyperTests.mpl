read "HyperInt.mpl":
interface(errorbreak=2, warnlevel=4):

_hyper_verbosity:=0:

_tests_failed := 0:
_tests_passed := 0:

Test := proc(expr, expected, label::string)
local transform:
global _tests_failed, _tests_passed:
	transform := [zeta[2]=Pi^2/6, seq(Zeta(2*n+1)=zeta[2*n+1], n=1..20)]:
	if simplify(eval(expr, transform))<>simplify(eval(expected, transform)) then
		_tests_failed := _tests_failed + 1:
		error "Test %1 FAILED: Expected %2, but got %3", label, expected, expr:
	else
		_tests_passed := _tests_passed + 1:
		printf("Test PASSED: %a\n", label):
	end if:
end proc:

GetParameters:=proc(expr)
	[op(remove(var->op(0,var) in {zeta,Zeta}, indets(expr)))]:
end proc:

TestIdentity := proc(eq, label::string := "")
local transform:
global _tests_failed, _tests_passed:
	transform := [zeta[2]=Pi^2/6, seq(Zeta(2*n+1)=zeta[2*n+1], n=1..20)]:
	subs(Int=HlogIntegrate, lhs(eq)-rhs(eq)):
	fibrationBasis(convert(%, `HlogRegInf`), GetParameters(eq)):
	if simplify(eval(%, transform))<>0 then
		_tests_failed := _tests_failed + 1:
		print(eq):
		error "Identity test %1 FAILED: Difference remained: %2", label, %%:
	else
		_tests_passed := _tests_passed + 1:
		printf("Identity test PASSED: %s\n", label):
	end if:
end proc:

HlogIntegrate := proc(expr, arg::equation)
	hyperInt(expr, arg):
	fibrationBasis(%, GetParameters(%)):
end proc:

################################################################################################################################
# Polylogarithms and associated functions, Lewin, chapters 1 and 6
################################################################################################################################
printf("Testing identities from \"Polylogarithms and associated functions\", Lewin, L.\n"):

#_hyper_algebraic_roots := false:
# Needs to be set true, since in fibrationBasis() of some polylog identities terms like x^2-x+1 occur...
_hyper_algebraic_roots := true:
_hyper_ignore_nonlinear_polynomials := false:

# To avoid Maple's own known identities and evaluations of polylogs, we write them as Mpl
# Helper function for convenient input of polylogs
Polylog := proc(arg)
	if not type(procname, `indexed`) then
		error "Order missing":
	end if:
	Mpl([op(procname)], [arg]):
end proc:

E :=
Polylog[2](z) = -Int(log(1-z)/z, z=0..z):
TestIdentity(E, "(1.4)"):

E :=
diff(Polylog[2](-1/x), x) = log(1+1/x)/x:
TestIdentity(E, "(1.6)"):

E :=
Polylog[2](-1/x) + Polylog[2](-x) = 2*Polylog[2](-1) - 1/2*log(x)^2:
TestIdentity(E, "(1.7)"):

E :=
2*Polylog[2](1) = 2*Polylog[2](-1) + Pi^2/2:
TestIdentity(E, "(1.8)"):

E :=
Polylog[2](1) = Pi^2/6:
TestIdentity(E, "(1.9)"):

E :=
Polylog[2](z) + Polylog[2](1-z) = Pi^2/6 - log(z)*log(1-z):
TestIdentity(E, "(1.11)"):

E :=
Polylog[2](x) + Polylog[2](-x/(1-x)) = -1/2*log(1-x)^2:
TestIdentity(E, "(1.12)"):

E :=
1/2*Polylog[2](x^2) = Polylog[2](x) + Polylog[2](-x):
TestIdentity(E, "(1.15)"):

E :=
Polylog[2](1/2) = Pi^2/12 - 1/2*log(2)^2:
TestIdentity(E, "(1.16)"):

E :=
Polylog[2](-x/(1-x)) + 1/2*Polylog[2](x^2) - Polylog[2](-x) = -1/2*log(1-x)^2:
TestIdentity(E, "(1.17)"):

E :=
Polylog[2](x/(1-x)*y/(1-y)) = Polylog[2](x/(1-y)) + Polylog[2](y/(1-x)) - Polylog[2](x) - Polylog[2](y) - log(1-x)*log(1-y):
TestIdentity(E, "(1.22)"):

E :=
Polylog[2](x/(1-x)*y/(1-y)) = Polylog[2](x/(1-y)) + Polylog[2](y/(1-x)) + Polylog[2](-x/(1-x)) + Polylog[2](-y/(1-y)) + 1/2*log((1-x)/(1-y))^2:
TestIdentity(E, "(1.23)"):

E :=
Polylog[2](x*(1-y)^2/y/(1-x)^2) = Polylog[2]((x-x*y)/(x-1)) + Polylog[2]((1-y)/(x*y-y)) + Polylog[2]((x-x*y)/(y-x*y)) + Polylog[2]((1-y)/(1-x)) + 1/2*log(y)^2:
TestIdentity(E, "(1.26)"):

E :=
Polylog[2](y*(1-x)/x/(1-y)) = Polylog[2](x) - Polylog[2](y) + Polylog[2](y/x) + Polylog[2]((1-x)/(1-y)) - Pi^2/6 + log(x)*log((1-x)/(1-y)):
TestIdentity(E, "(1.27)"):

E :=
Polylog[2](X+Y-X*Y) = Polylog[2](X) + Polylog[2](Y) - Polylog[2]((X*Y-Y)/X) - Polylog[2]((X*Y-X)/Y)
 + 1/2*log(X/Y)^2 + 2*Polylog[2](-1)
 - log((X+Y-X*Y)/X)*log((Y-X*Y)/X)
 - log((X+Y-X*Y)/Y)*log((X-X*Y)/Y):
TestIdentity(E, "(1.29)"):

E :=
Polylog[2](x) - Polylog[2](x/2) - Polylog[2]((1-x)/(2-x)) + Polylog[2]((2-2*x)/(2-x))
 = Pi^2/12 + 1/2*log(2)^2 - log(x)*log((2-2*x)/(2-x)):
TestIdentity(E, "(1.30)"):

E :=
Polylog[2](2*x-x^2) = 2*Polylog[2](x) - 2*Polylog[2](1/(2-x)) + Pi^2/6 - log(2-x)^2:
TestIdentity(E, "(1.31)"):

E :=
Polylog[2](-x^2) = 1/2*Polylog[2](x^2) + Polylog[2]((x^2+x)/(x-1)) + Polylog[2]((x-x^2)/(x+1)) + 1/2*log((1-x)/(1+x))^2:
TestIdentity(E, "(1.32)"):

E := 2*Polylog[2](x) + 2*Polylog[2](y) + 2*Polylog[2](-x*y/(x+y-x*y))
 = Polylog[2](x+y-x*y) + Polylog[2](x^2/(x+y-x*y)) + Polylog[2](y^2/(x+y-x*y)):
TestIdentity(E, "(1.43)"):

chi := x -> 1/2*Polylog[2](x) - 1/2*Polylog[2](-x):
E := 
chi(x) = 1/2*Int(log((1+x)/(1-x))/x, x=0..x):
TestIdentity(E, "(1.66)"):

E :=
chi((1-x)/(1+x)) + chi(x) = Pi^2/8 + 1/2*log(x)*log((1+x)/(1-x)):
TestIdentity(E, "(1.67)"):
chi := 'chi':

for n from 0 to 10 do
	E := Int(Polylog[2](x)*x^n, x=0..1) = Pi^2/6/(n+1) - harmonic(n+1)/(n+1)^2:
	TestIdentity(E, cat("(1.82), n=", n)):
end do:

E := Int(Polylog[2](t)/(1-x*t)^2, t=0..1) = Pi^2/6/(1-x) - Polylog[2](x)/x - log(1-x)^2/2/x:
TestIdentity(E, "(1.84)"):

E := Int(Polylog[2](t)/(1+t)^2, t=0..1) = ln(2)^2/2:
TestIdentity(E, "(1.85)"):

E := Int(Polylog[2](t)/(2-t)^2, t=0..1) = Pi^2/24:
TestIdentity(E, "(1.86)"):

forgetAll():
_hyper_splitting_field := {I}:
E :=
Pi*log(1+y) = Int(log(1+x^2*y^2)/(1+x^2), x=0..infinity):
TestIdentity(E, "(1.111)"):

E :=
Int(Polylog[2](-x^2*y^2)/(1+x^2), x=0..infinity) = 2*Pi*Polylog[2](-y):
TestIdentity(E, "(1.112)"):
_hyper_splitting_field := {}:
forgetAll():

E := Polylog[3](-x/(1-x)) + Polylog[3](1-x) + Polylog[3](x) = Polylog[3](1) + Pi^2/6*log(1-x) - 1/2*log(x)*log(1-x)^2 + 1/6*log(1-x)^3:
TestIdentity(E, "(6.10)"):

# substitute x->-x such that the formula holds for x>0
E := Polylog[3](x/(1+x)) + Polylog[3](1/(1+x)) + Polylog[3](-x) = Polylog[3](1) - Pi^2/6*log(1+x) - 1/2*log(x)*log(1+x)^2 + 1/3*log(1+x)^3:
TestIdentity(E, "(6.11)"):

E := Polylog[3](1/2) = 7/8*Polylog[3](1) - Pi^2/12*ln(2) + 1/6*ln(2)^3:
TestIdentity(E, "(6.12)"):

E := Polylog[2]((1-x)/(1+x)) - Polylog[2]((x-1)/(x+1)) + Polylog[2](x) - Polylog[2](-x) = Pi^2/4 + log(x)*log((1+x)/(1-x)):
TestIdentity(E, "(6.25)"):

E := Polylog[3]((1-x)/(1+x)) - Polylog[3]((x-1)/(x+1)) = log((1+x)/(1-x))*(Polylog[2](x) - Polylog[2](-x) - Pi^2/4 - 1/2*log(x)*log((1+x)/(1-x))) - 1/2*Int(log((1+x)/(1-x))^2/x, x=0..x):
# Constant term not given in the equation, so only check derivatives:
E := map(diff, E, x):
TestIdentity(E, "(6.26)"):

E :=
Int(log(1-z)^2/z, z=0..x) = log(x)*log(1-x)^2 + 2*log(1-x)*Polylog[2](1-x) - 2*Polylog[3](1-x) + 2*Polylog[3](1):
TestIdentity(E, "(6.27)"):

E :=
Int(log(1+z)^2/z, z=0..x) = log(x)*log(1+x)^2 - 2/3*log(1+x)^3 - 2*log(1+x)*Polylog[2](1/(1+x)) - 2*Polylog[3](1/(1+x)) + 2*Polylog[3](1):
TestIdentity(E, "(6.28)"):

E :=
Int(log(1-z^2)^2/z, z=0..x) = log(x)*log(1-x^2)^2 + log(1-x^2)*Polylog[2](1-x^2) - Polylog[3](1-x^2) + Polylog[3](1):
TestIdentity(E, "(6.29)"):

E := 1/2*log((1+x)/(1-x))^2 = 1/2*log(1+x)^2 + 1/2*log(1-x)^2 - log(1+x)*log(1-x):
TestIdentity(E, "(6.30)"):

E := 1/2*log(1-x^2)^2 = 1/2*log(1+x)^2 + 1/2*log(1-x)^2 + log(1+x)*log(1-x):
TestIdentity(E, "(6.31)"):

E := 1/2*Int(log((1+z)/(1-z))^2/z, z=0..x) 
= 7/2*Polylog[3](1) - 2*Polylog[3](1-x) - 2*Polylog[3](1/(1+x)) + 1/2*Polylog[3](1-x^2)
+ 1/3*log(1+x)^3 + log((1+x)/(1-x))*(Polylog[2](x) - Polylog[2](-x))
- 1/2*log(x)*log((1+x)/(1-x))^2 - Pi^2/6*(2*log((1+x)/(1-x)) + 1/2*log(1-x^2)):
TestIdentity(E, "(6.32)"):

E := Polylog[3]((1-x)/(1+x)) - Polylog[3]((x-1)/(x+1))
= 2*Polylog[3](1-x) + 2*Polylog[3](1/(1+x)) - 1/2*Polylog[3](1-x^2) - 7/4*Polylog[3](1) + Pi^2/6*log(1+x) - 1/3*log(1+x)^3:
TestIdentity(E, "(6.33)"):

E := Polylog[3]((1-x)/(1+x)) - Polylog[3]((x-1)/(x+1))
= 7/4*Polylog[3](1) - 2*Polylog[3](-x/(1-x)) - 2*Polylog[3](x/(1+x)) + 1/2*Polylog[3](-x^2/(1-x^2)) + Pi^2/4*log((1-x)/(1+x)) + 1/4*log((1+x)/(1-x))^2*log((1-x^2)/x^2):
TestIdentity(E, "(6.34)"):

E := Polylog[3](s+t-s*t)
= 2*Polylog[3](s) + 2*Polylog[3](t) + 2*Polylog[3](s/(s+t-s*t)) + 2*Polylog[3](t/(s+t-s*t))
+ 2*Polylog[3](-s*t/(s+t-s*t)) + 2*Polylog[3](-s/t) - Polylog[3](s^2/(s+t-s*t)) - Polylog[3](t^2/(s+t-s*t))
- 2*Polylog[3](1) + Pi^2/3*log((s+t-s*t)/t) + log(s/t)*log((s+t)/t)^2
+ log(s/t)^2*log((s+t-s*t)/(s+t)) - 1/3*(log((s+t-s*t)/s)^3 + log((s+t-s*t)/t)^3 + log((s+t)/t)^3 - log((s+t)/s)^3):
TestIdentity(E, "(6.92)"):

E := Polylog[3](s+t-s*t)
= 2*Polylog[3](s) + 2*Polylog[3](t) + 2*Polylog[3](s/(s+t-s*t)) + 2*Polylog[3](t/(s+t-s*t))
+ 2*Polylog[3](-s*t/(s+t-s*t)) + Polylog[3](-s/t) + Polylog[3](-t/s) - Polylog[3](s^2/(s+t-s*t))
- Polylog[3](t^2/(s+t-s*t)) - 2*Polylog[3](1) + (Pi^2/6 + 1/2*log(s/t)^2)*log((s+t-s*t)^2/s/t)
- 1/3*log((s+t-s*t)/s)^3 - 1/3*log((s+t-s*t)/t)^3:
TestIdentity(E, "(6.93)"):

E := Polylog[3](x*(1-y)^2/y/(1-x)^2)
= 2*Polylog[3](-x*(1-y)/(1-x)) + 2*Polylog[3](x*(1-y)/y/(1-x)) + 2*Polylog[3](-y*(1-x)/(1-y))
+ 2*Polylog[3]((1-x)/(1-y)) + 2*Polylog[3](x) + 2*Polylog[3](y) - Polylog[3](x*y)
- Polylog[3](x/y) - 2*Polylog[3](1) + Pi^2/3*log((1-y)/(1-x)) + log(-y)*log(1-y)^2
- log(-y)^2*log(1-x) - 1/3*log((1-y)/(1-x))^3 + 1/3*log(-y*(1-x)/(1-y))^3
+ 1/3*log(-(1-y)/y)^3 - 1/3*log(1-y)^3:
TestIdentity(E, "(6.96)"):

E := Polylog[2](x*(1-y)^2/y/(1-x)^2)
= Polylog[2](x*(1-y)/(x-1)) + Polylog[2]((1-y)/y/(x-1)) + Polylog[2](x*(1-y)/y/(1-x)) + Polylog[2]((1-y)/(1-x)) + 1/2*log(y)^2:
TestIdentity(E, "(6.97)"):

E := Polylog[2](x*(1-y)/y/(1-x)) = Polylog[2](y) - Polylog[2](x) + Polylog[2](x/y) + Polylog[2]((1-y)/(1-x)) - Pi^2/6 + log(y)*log((1-y)/(1-x)):
TestIdentity(E, "(6.100)"):

E := Polylog[2](x*y) = Polylog[2](x) + Polylog[2](y) + Polylog[2](x*(1-y)/(x-1)) + Polylog[2](y*(1-x)/(y-1)) + 1/2*log((1-x)/(1-y))^2:
TestIdentity(E, "(6.101)"):

E := Polylog[2](y*(1-x)/(y-1)) + Polylog[2]((y-1)/y/(1-x)) = -Pi^2/6 - 1/2*log(y*(1-x)/(1-y))^2:
TestIdentity(E, "(6.102)"):

E := Polylog[2]((1-y)/(1-x)) + Polylog[2]((1-y)/y/(x-1)) - Polylog[2](x*(1-y)/(x-1)) - Polylog[2](x*(1-y)/y/(1-x))
= 2*Polylog[2](x) - Polylog[2](x*y) - Polylog[2](x/y) - 1/2*log(y)^2:
TestIdentity(E, "(6.103)"):

E := Polylog[3](x*(1-y)^2/y/(1-x)^2) + Polylog[3](x*y) + Polylog[3](x/y)
- 2*Polylog[3](x*(1-y)/y/(1-x)) - 2*Polylog[3](x*(1-y)/(x-1)) - 2*Polylog[3]((1-y)/(1-x)) - 2*Polylog[3]((1-y)/y/(x-1))
- 2*Polylog[3](x) - 2*Polylog[3](y) + 2*Polylog[3](1)
= log(y)^2*log((1-y)/(1-x)) - Pi^2/3*log(y) - 1/3*log(y)^3:
TestIdentity(E, "(6.107)"):

E := Polylog[3]((x/(1-x))^3) + Polylog[3](x*(1-x)) - 3*Polylog[3](x/(1-x)) - 3/2*Polylog[3]((x/(1-x))^2) - 2*Polylog[3](x^2/(x-1)) - 2*Polylog[3](-x/(1-x)^2) + log(1-x)^3 = 0:
TestIdentity(E, "(6.108)"):

E := Polylog[3](-4*y/(1-y)^2) + 2*Polylog[3](-y) - 2*Polylog[3](y) - 4*Polylog[3](-2*y/(1-y)) - 4*Polylog[3]((1-y)/2)
= -7/2*Polylog[3](1) + Pi^2/3*log(2/(1-y)) - 2/3*log(2/(1-y))^3:
TestIdentity(E, "(6.109)"):

Y := (1-y)/(1+y):
E := Polylog[3](-Y^2) - 1/2*Polylog[3](Y^2) + Polylog[3](-y^2) - 1/2*Polylog[3](y^2) - 2*Polylog[3](Y*y) - 2*Polylog[3](-Y/y) + 5/4*Polylog[3](1) = log(Y)*log(y)^2 - Pi^2/3*log(y) - 1/3*log(y)^3:
TestIdentity(E, "(6.110)"):
Y:='Y':

Z := solve(X+Y+Z=X*Y*Z, Z):
E := Polylog[3](-X^2) + Polylog[3](-Y^2) + Polylog[3](-Z^2) - 2*Polylog[3](X*Y) - 2*Polylog[3](Y*Z) - 2*Polylog[3](Z*X)
- 2*Polylog[3](-X/Y) - 2*Polylog[3](-Y/Z) - 2*Polylog[3](-X/Z)
= 1/3*Pi^2*log(-Z/Y) + 1/3*log(-Z/Y)^3 + log(-Z/Y)^2*log(-X/Z) - 2*Polylog[3](1):
TestIdentity(E, "(6.131)"):
Z := 'Z':

################################################################################################################################
# Chapter 7: Higher-order functions
################################################################################################################################

for n from 2 to 10 do
	E := Polylog[n](z) = Int(Polylog[n-1](z)/z, z=0..z):
	TestIdentity(E, cat("(7.2), n=", n)):
end do:

E := Polylog[2](1) = Pi^2/6:
TestIdentity(E, "Even zetas, n=2"):
E := Polylog[4](1) = Pi^4/90:
TestIdentity(E, "Even zetas, n=4"):
E := Polylog[6](1) = Pi^6/945:
TestIdentity(E, "Even zetas, n=6"):
E := Polylog[8](1) = Pi^8/9450:
TestIdentity(E, "Even zetas, n=8"):

# (7.20)
for n from 1 to 8 do
	E := Polylog[n](-x) + (-1)^n*Polylog[n](-1/x) = -1/n!*log(x)^n + 2*add(log(x)^(n-2*r)/(n-2*r)!*Polylog[2*r](-1), r=1..floor(n/2));
	TestIdentity(E, cat("(7.20), n=", n)):
end do:

# (7.28), (7.29)
LewinB:=proc(r) bernoulli(2*r)*(-1)^(1+r): end proc:
for r from 1 to 4 do
	E := Polylog[2*r](1) = 2^(2*r-1)*LewinB(r)*Pi^(2*r)/(2*r)!;
	TestIdentity(E, cat("(7.28), r=", r)):
	E := Polylog[2*r](-1) = -(2^(2*r-1)-1)*LewinB(r)*Pi^(2*r)/(2*r)!;
	TestIdentity(E, cat("(7.29), r=", r)):
end do:

# (7.42), (7.43)
for n from 1 to 8 do
	E := Polylog[n](x^2)/2^(n-1) = Polylog[n](x) + Polylog[n](-x);
	TestIdentity(E, cat("(7.42), n=", n)):
	if n = 1 then next: fi:
	E := Polylog[n](-1) = -(1-2^(1-n))*Polylog[n](1);
	TestIdentity(E, cat("(7.43), n=", n)):
end do:

# (7.48)
for n from 2 to 8 do
	E := Polylog[n](z) = Polylog[n](1) + add((-1)^(k+1)/k!*log(z)^k*Polylog[n-k](z), k=1..n-1) + (-1)^(n-1)/(n-1)!*Int(log(w)^(n-1)/(1-w), w=1..z);
	TestIdentity(E, cat("(7.48), n=", n)) assuming z<1:
end do:

E := Polylog[4](x) = log(x)*Polylog[3](x) - 1/2*log(x)^2*Polylog[2](x) - 1/2*Int(log(x)^2*log(1-x)/x, x=0..x):
TestIdentity(E, "(7.61)"):

E := Polylog[4](x) = log(x)*Polylog[3](x) - 1/2*log(x)^2*Polylog[2](x) - 1/6*log(x)^3*log(1-x) - 1/6*Int(log(x)^3/(1-x), x=0..x):
TestIdentity(E, "(7.62)"):

E := 1/2*log(x)^2*log(1-x)^2 = Int(log(x)*log(1-x)^2/x, x=0..x) - Int(log(x)^2*log(1-x)/(1-x), x=0..x):
TestIdentity(E, "(7.63)"):

E := Polylog[4](-x/(1-x)) = log(x/(1-x))*Polylog[3](-x/(1-x)) - 1/2*log(x/(1-x))^2*Polylog[2](-x/(1-x)) + 1/6*log(x/(1-x))^3*log(1-x) + 1/6*Int(log(x/(1-x))^3/(1-x), x=0..x):
TestIdentity(E, "(7.64)"):

# (7.65)
Int(log(z)^2*log(1-z)/(1-z), z=0..x)
= -2*(Polylog[4](-x/(1-x)) + Polylog[4](x) - Polylog[4](1-x) + Polylog[4](1))
	+2*(log(1-x)*Polylog[3](x) - log(x)*Polylog[3](1-x))
	+2*log(x)*log(1-x)*Polylog[2](1-x)-Pi^2/6*log(1-x)^2
	+1/12*log(1-x)^2*(6*log(x)^2 + 4*log(x)*log(1-x)-log(1-x)^2)
	+2*Polylog[3](1)*log(x/(1-x)):
TestIdentity(%, "(7.65)") assuming x>0:

E := 1/8*Polylog[4](x^2) = Polylog[4](x) + Polylog[4](-x):
TestIdentity(E, "(7.80)"):

E := Polylog[4](-x) + Polylog[4](-1/x) = 2*Polylog[4](-1) -1/24*log(x)^4 - Pi^2/12*log(x)^2:
TestIdentity(E, "(7.81)"):

E := Polylog[4](-1) = -7*Pi^4/720:
TestIdentity(E, "(7.82)"):

xi := 1-x: eta := 1-y:
E := Polylog[3](x*y^2/eta/xi^2) + Polylog[3](x*eta) + Polylog[3](x/eta) - 2*Polylog[3](x*y/eta/xi) - 2*Polylog[3](-x*y/xi)
- 2*Polylog[3](y/xi) - 2*Polylog[3](-y/eta/xi) - 2*Polylog[3](x) - 2*Polylog[3](eta) + 2*Polylog[3](1)
= log(eta)^2*log(y/xi) - Pi^2/3*log(eta) - 1/3*log(eta)^3:
TestIdentity(E, "(7.85)"):

E := Polylog[3](y*x^2/xi/eta^2) + Polylog[3](y*xi) + Polylog[3](y/xi) - 2*Polylog[3](x*y/eta/xi) - 2*Polylog[3](-x*y/eta)
- 2*Polylog[3](x/eta) - 2*Polylog[3](-x/eta/xi) - 2*Polylog[3](y) -2*Polylog[3](xi) + 2*Polylog[3](1)
= log(xi)^2*log(x/eta) - Pi^2/3*log(xi) - 1/3*log(xi)^3:
TestIdentity(E, "(7.86)"):

E := Polylog[3](-y^2*x*xi/eta) + Polylog[3](-x*eta/xi) + Polylog[3](-x/xi/eta) - 2*Polylog[3](-x*y/eta) - 2*Polylog[3](x*y)
- 2*Polylog[3](y*xi) - 2*Polylog[3](-y*xi/eta) - 2*Polylog[3](-x/xi) - 2*Polylog[3](eta) + 2*Polylog[3](1)
= log(eta)^2*log(y*xi) - Pi^2/3*log(eta)-1/3*log(eta)^3:
TestIdentity(E, "(7.87)"):

E := Polylog[3](-x^2*y*eta/xi) + Polylog[3](-y*xi/eta) + Polylog[3](-y/xi/eta) - 2*Polylog[3](-x*y/xi) - 2*Polylog[3](x*y)
- 2*Polylog[3](x*eta) - 2*Polylog[3](-x*eta/xi) - 2*Polylog[3](-y/eta) - 2*Polylog[3](xi) + 2*Polylog[3](1)
= log(xi)^2*log(x*eta) - Pi^2/3*log(xi) - 1/3*log(xi)^3:
TestIdentity(E, "(7.88)"):

E :=
Polylog[4](-x^2*y*eta/xi) + Polylog[4](-y^2*x*xi/eta) + Polylog[4](x^2*y/eta^2/xi) + Polylog[4](y^2*x/xi^2/eta)
= 6*Polylog[4](x*y) + 6*Polylog[4](x*y/xi/eta) + 6*Polylog[4](-x*y/eta) + 6*Polylog[4](-x*y/xi)
	+3*Polylog[4](x*eta) + 3*Polylog[4](y*xi) + 3*Polylog[4](x/eta) + 3*Polylog[4](y/xi)
	+3*Polylog[4](-x*eta/xi) + 3*Polylog[4](-y*xi/eta) + 3*Polylog[4](-x/eta/xi) + 3*Polylog[4](-y/eta/xi)
	-6*Polylog[4](x) - 6*Polylog[4](y) - 6*Polylog[4](-x/xi) - 6*Polylog[4](-y/eta)
	+3/2*log(eta)^2*log(xi)^2:
TestIdentity(E, "(7.90)"):

E := Polylog[4](-x^3) + Polylog[4](x^3/xi^3)
= 3*Polylog[4](x*xi) + 3*Polylog[4](-x/xi^2) + 6*Polylog[4](-x^2/xi)
+ 18*Polylog[4](x) + 18*Polylog[4](-x/xi) + 27*Polylog[4](-x)
+ 27*Polylog[4](x/xi) + 3/4*log(xi)^4:
TestIdentity(E, "(7.91)"):

E := Polylog[4](-xi^3)-Polylog[4](x^3/xi^3)
= 3*Polylog[4](x*xi) - 3*Polylog[4](-x^2/xi) - 6*Polylog[4](-x/xi^2) + 18*Polylog[4](xi)
- 18*Polylog[4](-x/xi) + 27*Polylog[4](-xi) - 27*Polylog[4](x/xi) + 19*Pi^4/360 - 9/12*Pi^2*log(xi)^2
- 21/8*log(xi)^4 + 3*log(x)*log(xi)^3:
TestIdentity(E, "(7.93)"):

E := Polylog[5](-x) - Polylog[5](-1/x) = -1/120*log(x)^5 - Pi^2/36*log(x)^3 - 7*Pi^4/360*log(x):
TestIdentity(E, "(7.94)"):

E := 1/16*Polylog[5](x^2) = Polylog[5](x) + Polylog[5](-x):
TestIdentity(E, "(7.96)"):

E := Polylog[5](-1) = -15/16*Polylog[5](1):
TestIdentity(E, "(7.97)"):

# (7.99) Note the misprint of -9*Pi^2/4*log(xi)^3 instead of -9*Pi^2/12*log(xi)^3
E :=
Polylog[5](-x^3) + Polylog[5](-xi^3) + Polylog[5](x^3/xi^3)
= 9*Polylog[5](x*xi) + 9*Polylog[5](-x/xi^2)
	+9*Polylog[5](-x^2/xi) + 54*Polylog[5](x) + 54*Polylog[5](xi) + 54*Polylog[5](-x/xi)
	+81*Polylog[5](-x) + 81*Polylog[5](-xi) + 81*Polylog[5](x/xi) + 9/4*log(xi)^4*log(x)
	+19*Pi^4/120*log(xi) - 9*Pi^2/12*log(xi)^3 - 63/40*log(xi)^5 + 21*Polylog[5](1):
TestIdentity(E, "(7.99)"):
xi := 'xi': eta := 'eta':

# (7.128)
E := Int(log(z)^2*log(1-z)^2/z, z=0..1) = 8*zeta[5]-2/3*Pi^2*zeta[3]:
TestIdentity(E, "(7.128), eq. 1"):
E := Int(log(z)^3*log(1-z)^2/z, z=0..1) = 6*zeta[3]^2 - Pi^6/105:
TestIdentity(E, "(7.128), eq. 2"):

# Note the missing factor of 1/2 in the last term (it is still correctly written in 7.131)
for n from 0 to 7 do
	E := Int(log(y*(1-y))^n/(1-y), y=0..1/2) = -2^n*log(1/2)^(n+1)/(n+1) + coeff(series(exp(-Sum(p^m/m*(-1)^m*(2^m-2)*Zeta(m), m=2..infinity))-1, p=0, n+2), p, n+1)*n!/2:
	TestIdentity(E, cat("(7.132), n=", n)):
end do:

# (7.134)
for n from 1 to 7 do
	E := Int(log(y/(1-y))^n/(1-y), y=0..1/2) = (-1)^n*n!*Zeta(n+1)*(1-2^(-n)):
	TestIdentity(E, cat("(7.134), n=", n)):
end do:

F := (n,arg) -> Int(log(x)^(n-1)*log((1-x)/(1+x))^n/x, x=0..arg):
G := (n,arg) -> Int(log(x)^(n-1)*log(1-x)^n/x, x=0..arg):
for n from 1 to 3 do
	E := F(n,x) + F(n, (1-x)/(1+x)) = F(n,1) + 1/n*log(x)^n*log((1-x)/(1+x))^n:
	TestIdentity(E, cat("(7.183), n=", n)):
	E := G(n,x) + G(n,1-x) = G(n,1) + 1/n*log(x)^n*log(1-x)^n:
	TestIdentity(E, cat("(7.185), n=", n)):
	E := G(n,1/2) = 1/2*G(n,1) + 1/2/n*log(2)^(2*n):
	TestIdentity(E, cat("(7.186), n=", n)):
end do:
F := 'F':
G := 'G':

E := Polylog[2](x) = Polylog[2](y) - Int(log(1-z)/z, z=y..x):
TestIdentity(E, "(8.71)"):

E := Polylog[2](x) = Polylog[2](y) - log(1-y)*log(x/y) - 1/y*Int(log(1-z/(1-y))/(1+z/y), z=0..x-y):
TestIdentity(E, "(8.72)"):

E := Polylog[2](x) = Polylog[2](y) - Int(log(1-z*(x-y)/(1-y))/z/(1+y*z/(1-y)), z=0..1):
TestIdentity(E, "(8.77)"):

E := Polylog[2]((1+v)*w/(1+w)) + Polylog[2](-(1-v)*w/(1-w)) + Polylog[2]((1-v)*w/(1+w)) + Polylog[2](-(1+v)*w/(1-w)) - Polylog[2](-(1-v^2)*w^2/(1-w^2)) + 1/2*log((1+w)/(1-w))^2 = 0:
TestIdentity(E, "(8.80)"):

E := Polylog[2](x) + Polylog[2](x/(y-1)) + Polylog[2](y-x) + Polylog[2]((y-x)/(y-1)) - Polylog[2](x*(y-x)/(y-1)) + 1/2*log(1-y)^2 = 0:
TestIdentity(E, "(8.81)"):

# Section 8.3.4, equations without a number, at the end right before section 8.3.5
E := Int(Polylog[3](u)/(2-u)^3, u=0..1) = 1/2*zeta[3]-Pi^2/96 - Pi^2/32*ln(2):
TestIdentity(E, "page 267, section 8.3.4, eq. 1"):
E := Int(Polylog[3](u)/(1+u)^3, u=0..1) = 11/16*zeta[3] - Pi^2/12*ln(2) - 1/4*ln(2)^2:
TestIdentity(E, "page 267, section 8.3.4, eq. 2"):

# (8.105)
f := x -> log(x)*log(1-x)^2 + 2*log(1-x)*Polylog[2](1-x) - 2*Polylog[3](1-x) + 2*Polylog[3](1):

I8106 := Int((log(1-c*y)^2 + log(1-y)^2 - 2*log(1-y)*log(1-c*y))/y, y=0..x):
E := I8106 = f(c*x) + f(x) - 2*Int(log(1-y)*log(1-c*y)/y, y=0..x):
TestIdentity(E, "(8.106)"):

E := I8106 = Int(log(z)^2*(1/(c-z) - 1/(1-z)), z=1..(1-c*x)/(1-x)):
TestIdentity(E, "(8.107)"):

E := Int(log(z)^2/(c-z), z=1..(1-c*x)/(1-x)) = log(c)^2*log(1-x) + 2*log(c)*(Polylog[2]((c-1)/c/(1-x)) - Polylog[2]((c-1)/c)) - f((c-1)/c/(1-x)) + f((c-1)/c):
TestIdentity(E, "(8.108)"):

E := -Int(log(z)^2/(1-z), z=1..(1-c*x)/(1-x)) = f(x*(c-1)/(1-x)):
TestIdentity(E, "(8.109)"):

E := 2*Int(log(1-y)*log(1-c*y)/y, y=0..x)
= f(c*x) + f(x) - f(x*(c-1)/(1-x)) + f((c-1)/c/(1-x))
- f((c-1)/c) - log(1-x)*log(c)^2
- 2*log(c)*(Polylog[2]((c-1)/c/(1-x)) - Polylog[2]((c-1)/c)):
TestIdentity(E, "(8.110)"):

I8106 := 'I8106':
f := 'f':

E := Int(log(1-y)*log(1-c*y)/y, y=0..x)
= Polylog[3]((1-x*c)/(1-x)) + Polylog[3](1/c) + Polylog[3](1) - Polylog[3](1-c*x)
- Polylog[3](1-x) - Polylog[3]((1-c*x)/c/(1-x)) + log(1-c*x)*(Polylog[2](1/c) - Polylog[2](x))
+ log(1-x)*(Polylog[2](1-c*x) - Polylog[2](1/c) + Pi^2/6) + 1/2*log(c)*log(1-x)^2:
# This equation holds for 0<x<1/c<1; set c=1/x/(1+v) so that it holds for small x,v
E := eval(E, c=1/x/(1+v)):
TestIdentity(E, "(8.111)"):

# Appendix A.3.5
E := Int(log(1-y)*log(1-c*y)/y, y=0..x) = Polylog[3]((1-x*c)/(1-x)) - Polylog[3]((1-c*x)/c/(1-x))
- Polylog[3](1-x) - Polylog[3](1-c*x) + Polylog[3](1/c) + Polylog[3](1) + log(1-c*x)*(Polylog[2](1/c) - Polylog[2](x))
+ log(1-x)*(Polylog[2](1-c*x) - Polylog[2](1/c) + Pi^2/6)
+ 1/2*log(c)*log(1-x)^2:
# This identity holds for 0<x<1/c<1, change variables such that it holds for small 0<x,u
E := map(eval, E, c=1/(x+u)):
TestIdentity(E, "A.3.5. (1)"):

E := Int(log(1-z)^2/z, z=0..x) = log(x)*log(1-x)^2 + 2*log(1-x)*Polylog[2](1-x) - 2*Polylog[3](1-x) + 2*Polylog[3](1):
TestIdentity(E, "A.3.5. (6)"):

E := Int(log(1+z)^2/z, z=0..x) = log(x)*log(1+x)^2 - 2/3*log(1+x)^3 - 2*log(1+x)*Polylog[2](1/(1+x)) - 2*Polylog[3](1/(1+x)) + 2*Polylog[3](1):
TestIdentity(E, "A.3.5. (7)"):

E := Int(log(z)*log(1-z)/z, z=0..x) = Polylog[3](x) - log(x)*Polylog[2](x):
TestIdentity(E, "A.3.5. (8)"):

# Apparently wrong since diff(., x) and x->1 is zero on the lhs, but 3*zeta[2] on the rhs
#E := Int(log(z)*log(z-1)/z, z=1..x) = 1/3*log(x)^3 + log(x)*Polylog[2](1/x) - 2*Polylog[3](1/x) + 2*Polylog[3](1):
E := Int(log(z)*log(z-1)/z, z=1..x) = 1/3*log(x)^3 + log(x)*Polylog[2](1/x) + Polylog[3](1/x) - Polylog[3](1):
# Change variables such that E holds for small x
E := map(eval, E, x=1+x):
TestIdentity(E, "A.3.5. (9)"):

E := Int(log(z)^2*log(1-z)/z, z=0..x) = -2*Polylog[4](x) + 2*log(x)*Polylog[3](x) - log(x)^2*Polylog[2](x):
TestIdentity(E, "A.3.5. (10)"):

E := Int(log(z)^3/(1-z), z=0..x) = -6*Polylog[4](x) + 6*log(x)*Polylog[3](x) - 3*log(x)^2*Polylog[2](x) - log(x)^3*log(1-x):
TestIdentity(E, "A.3.5. (11)"):

E := Int(log(z)^2*log(1-z)/(1-z), z=0..x)
= 2*(Polylog[4](1-x) - Polylog[4](x) - Polylog[4](-x/(1-x)) - Polylog[4](1)) 
+ 2*(log(1-x)*Polylog[3](x) - log(x)*Polylog[3](1-x) + Polylog[3](1)*log(x/(1-x)))
+ 2*log(x)*log(1-x)*Polylog[2](1-x)
+ 1/12*log(1-x)^2*(6*log(x)^2 + 4*log(x)*log(1-x) - log(1-x)^2 - 2*Pi^2):
TestIdentity(E, "A.3.5. (12)"):

E := Int(log(x)*log(1-x)^2/x, x=0..1) = - Pi^4/180:
TestIdentity(E, "A.3.5. (13)"):
E := Int(log(x)^2*log(1-x)/(1-x), x=0..1) = - Pi^4/180:
TestIdentity(E, "A.3.5. (13)"):

################################################################################################################################
# Structural properties of Polylogarithms, Lewin
# Chapter 16
################################################################################################################################
printf("Testing identities from \"Structural properties of Polylogarithms\", Lewin, L.\n"):

forgetAll():
_hyper_splitting_field := {I}:
loadPeriods("periodLookups4thRoots.mpl"):

# (16.46): Mind the misprint of x^2 instead of x^(-2)
# Needs 4th roots of unity periods, therefore does not work
for n from 1 to 8 do
	for m from 1 to 8-n do
		# holds for odd n+m
		if (n+m) mod 2 = 0 then
			next:
		end if:
		E :=
		Int(Polylog[n](-x)*Polylog[m](-x^(-2))/x, x=0..infinity) = 2^(-n+2)*Pi^(n+m-1)/(n+m-1)!*(abs(euler(n+m-1))-2^(n+m+1)/n+m+1*abs(bernoulli(n+m+1))):
#		TestIdentity(E, cat("(16.46), n=", n, ", m=", m)):
	end do:
end do:

# (16.47)
E :=
Int(log(1+x)*log(1+x^(-2))/x, x=0..infinity) = Pi*Catalan - 3/8*Zeta(3):
#TestIdentity(E, "(16.47)"):

# (16.48)
for n from 1 to 8 do
	# Needs 4th roots of unity lookups
	if n>1 then
		next:
	end if:
	E := Int(Polylog[n](-x)*Polylog[n](-x^2)/x^3, x=0..infinity) = 2^(n-2)*Pi:
	TestIdentity(E, cat("(16.48), n=", n)):
end do:

# (16.50)
E :=
#Int(Polylog[2](-x)^2/x^(3/2), x=0..infinity) = 8*Pi/3*(Pi^2+24*log(2)):
Int(Polylog[2](-x^2)^2/x^(3)*2*x, x=0..infinity) = 8*Pi/3*(Pi^2+24*log(2)):
TestIdentity(E, "(16.50)"):

# (16.51)
E :=
#Int(Polylog[2](-x)^2/x^(5/2), x=0..infinity) = 8*Pi/27*(20-Pi^2-8*log(2)):
Int(Polylog[2](-x^2)^2/x^(5)*2*x, x=0..infinity) = 8*Pi/27*(20-Pi^2-8*log(2)):
TestIdentity(E, "(16.51)"):

# (16.52)
E :=
Int(log(1+x)*log(1+1/x^2), x=0..infinity) = 5*Pi^2/24 - Pi/2*(2-log(2)) + 2*Catalan:
TestIdentity(E, "(16.52)"):

# (16.53)
_hyper_max_pole_order:=15:
for n from 1 to 11 do
	for m from 1 to 11-n do
		E :=
		Int(Polylog[n](-x)*Polylog[m](-1/x)/x, x=0..infinity) = (m+n)*Zeta(m+n+1):
		TestIdentity(%, cat("(16.53), n=", n, ", m=", m)):
	end do:
end do:

# (16.54), involves eigth roots of unity
E :=
Int(log(1+x)*Polylog[2](-1/x)/x^(3/4), x=0..infinity) = -2*Pi*sqrt(2)*(5*Pi^2/3 + 16*(3*log(2)+Catalan - 4)):
#TestIdentity(E, "(16.54)"):

# (16.55), involves eigth roots of unity
E :=
Int(Polylog[2](-x)*Polylog[2](-1/x)/x^(3/4), x=0..infinity) = 256*Pi*sqrt(2)*(3-3*log(2) - Catalan):
#TestIdentity(E, "(16.55)"):

# (16.56)
E :=
#Int(Polylog[2](-x)*Polylog[2](-1/x)/x^(1/2), x=0..infinity) = 16*Pi*(3-4*log(2)):
Int(Polylog[2](-x^2)*Polylog[2](-1/x^2)/x*2*x, x=0..infinity) = 16*Pi*(3-4*log(2)):
TestIdentity(E, "(16.56)"):

# (16.57): Note the misprint of -Pi^4/40 instead of -Pi^4/30
E :=
Int(log(1+x)*Polylog[4](-x)/x^2, x=0..infinity) = -Pi^4/30 - Pi^2/3 - 2*Zeta(3) - 4*Zeta(5):
TestIdentity(E, "(16.57)"):

# (16.58)
E :=
Int(Polylog[3](-x)*Polylog[4](-x)/x^2, x=0..infinity) = 2*Pi^4/15 + 10*Pi^2/3 + 20*Zeta(3) + 4*Zeta(5):
TestIdentity(E, "(16.58)"):

forgetAll():
_hyper_splitting_field := {}:

################################################################################################################################
# Polylogarithms, Multiple Zeta Values and Superstring Amplitudes, Broedel, Schlotterer, Stieberger, hep-th > arXiv:1304.7267
################################################################################################################################
printf("Testing identities from \"Polylogarithms, Multiple Zeta Values and Superstring Amplitudes\", arXiv:1304.7267\n"):

# (5.27)
E :=
Hlog(z, [a1, 0, z]) = Hlog(z, [0, 0, a1]) - Hlog(z, [0, a1, a1]) - Hlog(z, [a1])*zeta[2]:
Test(fibrationBasis(convert(lhs(E), HlogRegInf), [z,a1]), rhs(E), "(5.27), eq. 1"):

E:=
Hlog(z, [a1, z, a2]) = Hlog(z, [a1 , a1 , a2]) - Hlog(z, [a2 , 0, a1]) + Hlog(z, [a2 , a1, a1]) - Hlog(z, [a2, a1, a2]):
Test(fibrationBasis(convert(lhs(E), HlogRegInf), [z, a1, a2]), rhs(E), "(5.27), eq. 2"):

# (E.1)
E := [
	Hlog(z, [a1, z]) = -Hlog(z, [0, a1 ]) + Hlog(z, [a1, a1 ]),
	Hlog(z, [0, z, a1 ]) = Hlog(z, [0, 0, a1]) - Hlog(z, [a1, 0, a1 ]) - Hlog(z, [a1 ])*zeta[2],
	Hlog(z, [0, a1, z]) = -2*Hlog(z, [0, 0, a1]) + Hlog(z, [0, a1, a1 ]) + Hlog(z, [a1, 0, a1 ]) + Hlog(z, [a1])*zeta[2],
	Hlog(z, [a1, 0, z]) = Hlog(z, [0, 0, a1]) - Hlog(z, [0, a1 , a1 ]) - Hlog(z, [a1 ])*zeta[2],
	Hlog(z, [a1, z, z]) = Hlog(z, [0, 0, a1]) - Hlog(z, [0, a1 , a1 ]) - Hlog(z, [a1 , 0, a1]) + Hlog(z, [a1 , a1 , a1]),
	Hlog(z, [a1, z, a2 ]) = Hlog(z, [a1, a1, a2]) - Hlog(z, [a2, 0, a1 ]) + Hlog(z, [a2 , a1 , a1 ]) - Hlog(z, [a2 , a1 , a2])
]:
for n from 1 to nops(E) do
	Test(fibrationBasis(convert(lhs(E[n]), HlogRegInf), [z, a1, a2]), rhs(E[n]), cat("(E.1), eq. ", n)):
end do:

# (E.2)
E :=
Hlog(z, [a1, a2, z]) = -Hlog(z, [0, a1 , a2]) - Hlog(z, [a1 , 0, a2]) + Hlog(z, [a1 , a2 , a2]) + Hlog(z, [a2, 0, a1]) - Hlog(z, [a2 , a1 , a1]) + Hlog(z, [a2 , a1 , a2]):
Test(fibrationBasis(convert(lhs(E), HlogRegInf), [z, a1, a2]), rhs(E), "(E.2)"):
 
################################################################################################################################
# Various
################################################################################################################################

# Calculated by Pen and Paper:
TestIdentity(0 = -Hlog(1-x, [0,1])-Zeta(2)-Hlog(x, [0,1])+ln(x)*Hlog(x, [1]));
TestIdentity(0 = -Hlog(1-x, [0,0,1]) - Zeta(3)-Zeta(2)*Hlog(x, [1])+ln(x)*Hlog(x, [1, 1])-Hlog(x, [0,1,1])-Hlog(x, [1,0,1]));
TestIdentity(0 = Hlog(1-x, [1,0,1]) + 2*Zeta(3)+2*Hlog(x, [0,0,1])+ln(x)*(Zeta(2)-Hlog(x, [0,1]))):
TestIdentity(0 = Hlog(1-x, [0,1,1]) - Zeta(3)-(1/2)*ln(x)^2*Hlog(x, [1])+ln(x)*Hlog(x, [0,1])-Hlog(x, [0,0,1]));
TestIdentity(0 = -Hlog(1-1/x, [0,1]) + ((1/2)*ln(x)^2-ln(x)*Hlog(x, [1])+Zeta(2)+Hlog(x, [0,1])));
TestIdentity(0 = -Hlog(1-1/x, [0,0,1]) - (1/6)*ln(x)^3+(1/2)*ln(x)^2*Hlog(x, [1])-Hlog(x, [0,0,1])-ln(x)*Hlog(x, [1, 1])+Hlog(x, [0,1,1])+Hlog(x, [1,0,1])-Zeta(2)*ln(x)+Zeta(2)*Hlog(x, [1]));
TestIdentity(0 = Hlog(-1/x, [0,1,1])-Zeta(3)+(1/6)*ln(x)^3-Hlog(x, [0,-1])*ln(x)+Hlog(x, [0,0,-1])+Hlog(x, [0,-1,-1]));
TestIdentity(0 = Hlog(-1/x, [1,0,1]) + (1/6)*ln(x)^3-(Zeta(2)+(1/2)*ln(x)^2)*Hlog(x, [-1])+ln(x)*(Zeta(2)+Hlog(x, [0,-1]))+2*Zeta(3)-2*Hlog(x, [0,0,-1])+Hlog(x, [-1, 0, -1])):


# Bubble-Chain identity
for p from 1 to 11 do
	E :=
	Int((1/x-1/(x-z))*Polylog[p](-x+z)-1/x*Polylog[p](z/(x+1)), x=0..infinity) = p*Polylog[p+1](z):
	TestIdentity(E, cat("Bubble-Chain identity, p=", p)):
end do:

# Multiple Zeta Values and periods of moduli spaces, F. Brown

E :=
Int(Int(1/(1-x*y), y=0..1), x=0..1) = zeta[2]:
TestIdentity(E, "math/0606419 (8.5), I_1"):

E :=
Int(Int(Int(1/(1-t1)/t2/(t3-t1), t1=0..t2), t2=0..t3), t3=0..1) = 2*zeta[3]:
TestIdentity(E, "math/0606419 (8.6), I_2"):

E :=
Int(Int(Int(1/(1-t1)/t3/(t3-t1), t1=0..t2), t2=0..t3), t3=0..1) = zeta[2]:
TestIdentity(E, "math/0606419 (8.8), I_3"):

# Euler's Beta function
newIntegration():
N := 12:
_hyper_max_pole_order := N:
X := []:
for n from 0 to N do
	for m from 0 to N-n do
		X := [op(X), [(-x)^n*y^m/((1+a)^2*factorial(n)*factorial(m)), [`$`([-a-1], n), `$`([-a], m)]]]
	end do:
end do:
X := fibrationBasis(integrationStep(X, a), []):
B := series(Beta(1-y*t, 1-x*t+y*t), t = 0, N+1):
B := simplify(add(coeff(B, t, n), n = 0 .. N)):
Test(simplify(subs([seq(z[n] = Zeta(n), n = 2 .. 20)], X)), B, "Beta-function"):
N:='N': X:='X': B:='B':

# Ising-type integrals
printf("Ising-type integrals E_n of \"Integrals of the Ising class\", Bailey, Borwein, Crandall\n"):

IsingE := proc(n::integer)
local f, u, k:
	u := k -> mul(t[i],i = 1 .. k):
	f := [[2,[]]]:
	for k from n to 2 by -1 do
		f := scalarMul(f, mul((u(k)-u(j))/(u(k)+u(j)), j = 1 .. k-1)^2/(1+x)^2):
		f := integrationStep(eval(f, t[k]=1/(1+x)), x):
	end do:
	fibrationBasis(f, []):
end proc:
Results := [
2,
6-8*ln(2),
10 - 2*Pi^2 - 8*ln(2) + 32*ln(2)^2,
22 - 82*Zeta(3) - 24*ln(2) + 176*ln(2)^2 - 256*ln(2)^3/3 + 16*Pi^2*ln(2) - 22*Pi^2/3,
42 - 1984*Polylog[4](1/2) + 189*Pi^4/10 - 74*Zeta(3) - 1272*Zeta(3)*ln(2) + 40*Pi^2*ln(2)^2 - 62*Pi^2/3 + 40*Pi^2*ln(2)/3 + 88*ln(2)^4 + 464*ln(2)^2 - 40*ln(2)
]:
for n from 1 to nops(Results) do
	TestIdentity(IsingE(n)=Results[n], cat("Ising E_", n)):
end do:

################################################################################################################################
# Feynman Integrals
################################################################################################################################
printf("Testing Feynman integrals\n"):

forgetAll():
_hyper_splitting_field := {}:
_hyper_algebraic_roots := true:

# Renormalized bubble-chain graphs
bubbleRational := proc (n)
local res, vars, S, p;
	vars := {seq(x[i], i = 1 .. n)}:
	# Assemble integrand
	p := mul(x, `in`(x, vars)):
	res := [[(-1)^(n+1)/p, []]]:
	for S in combinat[powerset](vars) do
		if S = {} or S = vars then next end if:
		res := [op(res), eval([(-1)^nops(S)/(p*z), [[-1-z]]], z = add(x, `in`(x, `minus`(vars, S)))/add(x, `in`(x, S)))]:
	end do:
	# Integrate
	newIntegration():
	simplify(fibrationBasis(hyperInt(res, [seq(x[i], i = 2 .. n)]), [x[1]])):
end proc:

for n from 2 to 5 do 
	Test(bubbleRational(n), n!/x[1], cat("Bubble chains with rational momentum flow, n=", n)): 
end do:

bubbleIrrational := proc (n, m)
local res, p, XX, YY, X, Y, Xc, Yc, xvars, yvars, xs, ys:
	xvars := {seq(x[i], i = 1 .. n)}:
	yvars := {seq(y[i], i = 1 .. m)}:
	# Assemble integrand
	XX := add(x, `in`(x, xvars)):
	YY := add(y, `in`(y, yvars)):
	p := mul(x, `in`(x, `union`(xvars, yvars))):
	res := [[(-1)^(n+m+1)/p, []]]:
	for xs in combinat[powerset](xvars) do
		for ys in combinat[powerset](yvars) do
			if `union`(xs, ys) = {} or `union`(xs, ys) = `union`(xvars, yvars) then next end if:
			X := add(x, `in`(x, xs)):
			Xc := XX-X: 
			Y := add(y, `in`(y, ys)):
			Yc := YY-Y:
			if not xs = xvars then
				res := [op(res), [(-1)^(nops(xs)+nops(ys))*(X+Y)/(p*Xc), [[-(XX+Y)*(Xc+Yc)/(Xc*Yc+(X+Y)*(Xc+Yc))]]]]:
			end if:
			if not ys = yvars then
				res := [op(res), [(-1)^(nops(xs)+nops(ys))*(X+Y)/(p*Yc), [[-(X+YY)*(Xc+Yc)/(Xc*Yc+(X+Y)*(Xc+Yc))]]]]:
			end if:
			if not (xs = xvars or ys = yvars) then
				res := [op(res), [(-1)^(nops(xs)+nops(ys))/p, [[-(XX+Y)*(Xc+Yc)*(X+YY)/((Xc*Yc+(X+Y)*(Xc+Yc))*(XX+YY))]]]]:
			end if:
		end do:
	end do:
	# Integrate
	newIntegration():
	xvars := [op(xvars), op(yvars)]:
	res := hyperInt(eval(res, xvars[-1]=1), xvars[1..-2]):
	simplify(fibrationBasis(res, [])):
end proc:

bubbleIrrationalGamma := proc(n, m)
local res:
	# Generating function
	res := GAMMA(1-x)*GAMMA(1-y)*GAMMA(1+x+y)/(GAMMA(x+1)*GAMMA(1+y)*GAMMA(2-x-y)):
	if n=0 then
		res := eval(res, x=0):
	else
		res := eval(diff(res, x$n), x=0):
	end if:
	if m=0 then
		res := eval(res, y=0):
	else
		res := eval(diff(res, y$m), y=0):
	end if:
	simplify(res):
end proc:

for n in [[2,0], [1,1], [1,2], [5,0], [1,4], [2,3], [1,5], [2,4], [3,3]] do
	Test(bubbleIrrational(op(n)), bubbleIrrationalGamma(op(n)), cat("Bubble chains with transversal momentum flow, (n,m)=(", n[1], ",", n[2], ")")):
end do:

# Wheels with spokes in D=4
_hyper_algebraic_roots:=true:

edges := [[1, 2], [1, 3], [1, 4], [2, 3], [3, 4], [4, 2]]:
psi := graphPolynomial(edges):
vars := [x[1], x[2], x[3], x[4], x[5], x[6]]:
newIntegration():
hyperInt([[1/psi^2, []]], vars[1..-2]):
Test(fibrationBasis(%, [vars[-1]]), 6*Zeta(3)/vars[-1], "Wheel with 3 spokes"):

edges := [[1, 2], [1, 3], [1, 4], [1, 5], [2, 3], [3, 4], [4, 5], [5, 2]]:
psi := graphPolynomial(edges):
vars := [x[1], x[2], x[5], x[6], x[8], x[3], x[4], x[7]]:
newIntegration():
hyperInt([[1/psi^2, []]], vars[1..-2]):
Test(fibrationBasis(%, [vars[-1]]), 20*Zeta(5)/vars[-1], "Wheel with 4 spokes"):

edges := [[1, 2], [1, 3], [1, 4], [1, 5], [1, 6], [2, 3], [3, 4], [4, 5], [5, 6], [6, 2]]:
psi := graphPolynomial(edges):
vars := [x[1], x[2], x[6], x[7], x[10], x[3], x[8], x[9], x[4], x[5]]:
newIntegration():
#hyperInt([[1/psi^2, []]], vars[1..-2]):
#Test(fibrationBasis(%, [vars[-1]]), 70*Zeta(7)/vars[-1], "Wheel with 5 spokes"):

# One-loop vertex periods (these are rational integrals without any polylogarithms)
testOneLoop := proc (n)
	local vars, psi:
	vars := [seq(x[i], i = 1 .. n)]:
	psi := add(x, `in`(x, vars)):
	newIntegration():
	Test(hyperInt([[1/psi^n, []]], vars[2 .. n]), [[1/(factorial(n-1)*vars[1]), []]], cat("One-loop ", n)):
end proc;
for n to 20 do testOneLoop(n) end do:

# Simple graphs
Test(hyperInt([[1/((a+A)*(b+B+C+c)+(b+B)*(c+C))^3, []]], [C, B, A, a, c]), [[1/(2*b), []]], "Two-loop phi^3 vertex"):
Test(hyperInt([[a*b*c/(a*b+a*c+b*c)^3, []]], [c, b]), [[1/(2*a), []]], "Two-loop phi^3 vertex"):
Test(hyperInt([[1/2*(1/((a+b)*(c+d)+c*d)^2+1/((a+b)*(c+d)+a*b)^2-1/((a+b)^2*(c+d)^2)), []]], [d, c, b]) , [[1/a, []]], "Dunce's cap"):

if _tests_failed = 0 then
	printf("ALL %a TESTS PASSED SUCCESSFULLY!\n", _tests_passed):
else
	printf("%a TESTS FAILED\n", _tests_failed):
	error "There were %1 failed tests", _tests_failed:
end if:
