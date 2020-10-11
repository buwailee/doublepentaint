# Copyright (C) 2014 Erik Panzer, panzer@mathematik.hu-berlin.de

_hyper_check_divergences := false:
_hyper_algebraic_roots := false:
_hyper_ignore_nonlinear_polynomials := true:
forgetAll():

# Ising-type integrals of class E
IsingE := proc(n::integer)
local f, u, k:
	u := k -> mul(t[i],i = 1 .. k):
	f := [[2,[]]]:
	for k from n to 2 by -1 do
		f := scalarMul(f, mul((u(k)-u(j))/(u(k)+u(j)), j = 1 .. k-1)^2/(1+x)^2):
		f := integrationStep(eval(f, t[k]=1/(1+x)), x):
	end do:
	fibrationBasis(f):
end proc:

# Exact results up to weight 8
E := table([(2)=6-8*ln(2),(3)=32*ln(2)^2-12*zeta[2]-8*ln(2)+10,(4)=22+96*ln(2)
*zeta[2]-24*ln(2)-44*zeta[2]-82*zeta[3]+176*ln(2)^2-256/3*ln(2)^3,(5)=42-124*
zeta[2]-992*zeta[1,-3]-74*zeta[3]-318/5*zeta[2]^2-40*ln(2)+464*ln(2)^2+80*ln(2
)*zeta[2]+512/3*ln(2)^4-256*ln(2)^2*zeta[2]+464*ln(2)*zeta[3],(6)=86-88*ln(2)+
768*ln(2)^4+704/3*ln(2)^3+1360*ln(2)^2-13964*zeta[2]*zeta[3]-348*zeta[2]-6048*
zeta[1,-3]+134*zeta[3]+53775/2*zeta[5]+27904*zeta[1,1,-3]+830*zeta[2]^2-2632*
ln(2)*zeta[3]-272*ln(2)*zeta[2]+512*ln(2)^2*zeta[2]+1024/3*ln(2)^3*zeta[2]+384
*ln(2)^2*zeta[3]-3216/5*ln(2)*zeta[2]^2+11520*ln(2)*zeta[1,-3]-4096/15*ln(2)^5
,(7)=170-32624*zeta[2]*zeta[3]+512/3*ln(2)^3*zeta[2]+6400*ln(2)^2*zeta[3]-9304
*ln(2)*zeta[2]^2+19840*ln(2)*zeta[1,-3]+2336*ln(2)^2*zeta[2]-12472*ln(2)*zeta[
3]+69056/5*ln(2)^2*zeta[2]^2-64000*ln(2)^2*zeta[1,-3]-340588*ln(2)*zeta[5]-\
312320*ln(2)*zeta[1,1,-3]-8320*zeta[2]*zeta[1,-3]-20992/3*ln(2)^3*zeta[3]-688*
ln(2)*zeta[2]-168*ln(2)-844*zeta[2]-21696*zeta[1,-3]+350*zeta[3]+149851/2*zeta
[5]+63616*zeta[1,1,-3]+942624*zeta[1,-5]-575488*zeta[1,1,1,-3]+18402/5*zeta[2]
^2+4209858/35*zeta[2]^3-380881*zeta[3]^2+2432*ln(2)^4+4096/15*ln(2)^5+161760*
ln(2)*zeta[2]*zeta[3]+3280*ln(2)^2+832*ln(2)^3+16384/45*ln(2)^6,(8)=342+
33352925/17*zeta[2]*zeta[5]+211456*zeta[2]*zeta[1,1,-3]+282176*zeta[3]*zeta[1,
-3]-8206978/17*zeta[2]^2*zeta[3]-54575568/35*ln(2)*zeta[2]^3+4757064*ln(2)*
zeta[3]^2-62372*zeta[2]*zeta[3]+256*ln(2)^3*zeta[2]+17072*ln(2)^2*zeta[3]-\
169624/5*ln(2)*zeta[2]^2+22656*ln(2)*zeta[1,-3]+77824/3*ln(2)^4*zeta[3]-\
1022464/15*ln(2)^3*zeta[2]^2+655360/3*ln(2)^3*zeta[1,-3]+1977632*ln(2)^2*zeta[
5]+1761280*ln(2)^2*zeta[1,1,-3]-12015360*ln(2)*zeta[1,-5]+7045120*ln(2)*zeta[1
,1,1,-3]-16384/15*ln(2)^5*zeta[2]+11424*ln(2)^2*zeta[2]-53064*ln(2)*zeta[3]+
591744/5*ln(2)^2*zeta[2]^2-294912*ln(2)^2*zeta[1,-3]-1819522*ln(2)*zeta[5]-\
1697792*ln(2)*zeta[1,1,-3]+32128*zeta[2]*zeta[1,-3]+28672/3*ln(2)^4*zeta[2]-\
210176/3*ln(2)^3*zeta[3]-2960*ln(2)*zeta[2]-344*ln(2)-2060*zeta[2]-84704*zeta[
1,-3]+1790*zeta[3]+340095/2*zeta[5]+192128*zeta[1,1,-3]-230302165/136*zeta[7]+
1493504/17*zeta[1,1,-5]-62466560/17*zeta[1,3,-3]+6195680*zeta[1,-5]-3602432*
zeta[1,1,1,-3]+12926976*zeta[1,1,1,1,-3]+76958/5*zeta[2]^2+4034546/5*zeta[2]^3
-2434920*zeta[3]^2+7488*ln(2)^4+2048*ln(2)^5-131072/315*ln(2)^7-818624*ln(2)^2
*zeta[2]*zeta[3]+40960*ln(2)*zeta[2]*zeta[1,-3]+687888*ln(2)*zeta[2]*zeta[3]+
8080*ln(2)^2+2752*ln(2)^3+57344/45*ln(2)^6]):
CPU := table([(2)=.040994,(3)=.051992,(4)=.234964,(5)=2.017692,(6)=40.622825,(
7)=1760.027435,(8)=100275.371827]):
Alloc := table([(2)=53493760,(3)=53493760,(4)=79749120,(5)=375910400,(6)=
1735897088,(7)=2013216768,(8)=32091615232]):