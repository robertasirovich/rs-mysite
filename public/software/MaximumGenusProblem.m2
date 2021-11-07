--**********************************************************************--
-- ANCILLARY FILE TO THE PAPER                                          --
-- "THE MAXIMUM GENUS PROBLEM FOR LOCALLY COHEN-MACAULAY SPACE CURVES"  --
-- BY VALENTINA BEORCHIA, PAOLO LELLA AND ENRICO SCHLESINGER            --
--**********************************************************************--

---------------------------------------------------------------------------------------
-- Example 5.4: general WT-homogeneous polynomial and explicit proof of Conjecture B --
---------------------------------------------------------------------------------------
restart
printWidth=100;
KK = QQ;
m = 2, l = 3*m-2
S = KK[z,x,y,Degrees=>{3,1,2},MonomialOrder=>Lex];
multipleLine = (ideal(x,y))^l;
R = S/multipleLine;
supportG = rsort flatten entries basis(3*m,R)
N = #supportG - 1
A = KK[a_0..a_N];
AS = A[gens S,MonomialOrder=>Lex];
AR = AS/(ideal(AS_1,AS_2))^l;
fromRtoAR = map(AR,R);
g = sum for i from 0 to N list A_i*(fromRtoAR supportG#i) -- generic g

-- cf. Proposition 5.2 and Remark 5.3
WThomogeneousPiecesPhi = {};
for n from 3*m to 9*(m-1) do (
    basisRnMinus3m = rsort flatten entries basis(n-3*m,R);
    basisMn = select(rsort flatten entries basis(n,R),t -> (sum for g in gens R list degree(g,t)) >= l);
    phi = matrix for b in basisRnMinus3m list for t in basisMn list leadCoefficient((g*(fromRtoAR b))//(fromRtoAR(t)));
    print ("\n--------------------------------------------------------------------------------");
    print ("Phi_" | toString(n) | ": R[-" | toString(3*m) | "]_" | toString(n) | " -> M_" | toString(n));
    print phi;    	   
    WThomogeneousPiecesPhi = append(WThomogeneousPiecesPhi,phi);
)
determinants = sort for phi in WThomogeneousPiecesPhi list det phi;
nonZero = {};
for p in determinants do 
(
   nonConstantFactors = select(factor p, f -> first degree f#0 > 0);
   nonZero = nonZero | for f in nonConstantFactors list f#0; 
)
sort unique nonZero 

---------------------------------------------------------------------------------------
-- Proof of Conjecture B for large m (cf. end of Section 5)                          --
---------------------------------------------------------------------------------------
restart
printWidth=100;
KK = ZZ/10007;
R = KK[x,y,z,Degrees=>{1,2,3}];
S = KK[gens R,MonomialOrder=>GLex];
fromRtoS = map(S,R);
repeat = false;
m = 2; M = 40;
while m <= M do
(
    if not repeat then
    (
    	print ("\n--------------------------------------------------------------------------------");
    	print ("\tProof of Conjecture B for m = " | toString(m));
	l = 3*m-2;
    	multipleLine := (ideal(S_0,S_1))^l;
    	J = (ideal gens S)^l;
    );
    g = random(3*m,R);
    I = ideal fromRtoS g + multipleLine;
    print ("\t    -- Computing the initial ideal of (x,y)^"|toString(l)| " + g ...");
    inI = trim ideal leadTerm I;
    conjectureVerified = (inI == J);
    if conjectureVerified then
    (
    	print ("\tLT ((x,y)^"|toString(l)| " + g) == (x,y,z)^"|toString(l)| ": " | toString(conjectureVerified));
	m = m+1;
	repeat = false;
    )
    else
    (
	print ("\tRandom choice not generic. Retry ... ");
    	repeat = true;	
    );
)

---------------------------------------------------------------------------------------
-- Construction of curves of degree d whose genus realizes the bound P(d,d)          --
-- (cf. Introduction after Conjecture A and Theorem 1.2)                             --
---------------------------------------------------------------------------------------
restart
printWidth=100;
KK = ZZ/10007;
P = (d,s) -> ( 
  if s <= d and d <= 2*s then 
      (s-1)*d+1-binomial(s+2,3) 
  else if d > 2*s then 
      binomial(d-s,2)-binomial(s-1,3)
);
R = KK[x,y,z,Degrees=>{1,2,3}];
m = 3;
l = 3*m-2;
d = 3*m-1;
multipleLine = (ideal(x,y))^l
g = random(3*m,R)%multipleLine
S = KK[X,Y,Z,W];
fromRtoS = map(S,R,{X,Y,Z})
G = homogenize( fromRtoS g,W) 

-- CASE 1. d = 3*m-1 (d = 2 mod 3)
F1 = X*G - Y*W^(d-1)
C1 = saturate trim((ideal(X,Y))^d + ideal F1)
C1 = removeLowestDimension C1;
dC1 = degree C1, gC1 = genus C1
dC1 == 3*m-1, P(dC1, dC1) == gC1
-- postulation (checking whether the curve is contained in a surface of degree 3*m-2)
binomial(3+dC1-1,3)-hilbertFunction(dC1-1,C1)
-- Rao function (checking whether the curve in LCM)
raoFunction = {};
sheafC1 = sheaf module C1;
j = 3*m-3; while (rho = rank HH^1(sheafC1(j))) != 0 do (j = j - 1; raoFunction = prepend(rho,raoFunction));
raoFunction

-- CASE 2. d = 3*m (d = 0 mod 3)
F2 = X*G*Z - Y*W^d
C2 = saturate trim((ideal(X,Y))^d + ideal F2)
C2 = removeLowestDimension C2;
C2plusL = trim intersect (C2, ideal(Z,W));
dC2plusL= degree C2plusL, gC2plusL = genus C2plusL
dC2plusL == 3*m, P(dC2plusL, dC2plusL) == gC2plusL
-- postulation (checking whether the curve is contained in a surface of degree 3*m-1)
binomial(3+dC2plusL-1, 3) - hilbertFunction(dC2plusL-1, C2plusL)
-- Rao function (checking whether the curve in LCM)
raoFunction = {};
sheafC2plusL = sheaf module C2plusL;
j = 3*m-2; while (rho = rank HH^1(sheafC2plusL(j))) != 0 do (j = j - 1; raoFunction = prepend(rho,raoFunction));
raoFunction

-- CASE 3. d = 3*m+1 (d = 1 mod 3)
F3 = X*G*Z^2 - Y*W^(d+1)
C3 = saturate trim((ideal(X,Y))^d + ideal F3)
C3 = removeLowestDimension C3;
C3plus2L = saturate intersect (C3, ideal(Z^2,Z*W,W^2,X^(d+1)*Z-Y^(d+1)*W));
dC3plus2L = degree C3plus2L, gC3plus2L = genus C3plus2L
dC3plus2L == 3*m+1, P(dC3plus2L, dC3plus2L) == gC3plus2L
-- postulation (checking whether the curve is contained in a surface of degree 3*m)
binomial(3+dC3plus2L-1, 3) - hilbertFunction(dC3plus2L-1, C3plus2L)
-- Rao function (checking whether the curve in LCM)
raoFunction = {};
sheafC3plus2L = sheaf module C3plus2L;
j = 3*m-1; while (rho = rank HH^1(sheafC3plus2L(j))) != 0 do (j = j - 1; raoFunction = prepend(rho,raoFunction));
raoFunction
