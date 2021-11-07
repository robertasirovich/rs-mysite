-----------------------------------------------------
--        Hilbert scheme of 2 points in P^2        --
-----------------------------------------------------
restart
KK = ZZ/10007;
IG = Grassmannian(1,5,CoefficientRing=>KK,Variable=>D);
G = ring(IG);

-- Exterior algebra of polynomials of degree 2 in 3 variables
E = G[e_0..e_5,SkewCommutative=>true];

-- Exterior algebra of polynomials of degree 3 in 3 variables
F = G[f_0..f_9,SkewCommutative=>true];

-- Multiplication maps
m2 = map(F,E,{f_0,f_1,f_2,f_4,f_5,f_7});
m1 = map(F,E,{f_1,f_2,f_3,f_5,f_6,f_8});
m0 = map(F,E,{f_4,f_5,f_6,f_7,f_8,f_9});

-- Generator of the fourth exterior power of the homogeneous piece of degree 2 of the ideal
Plucker = sort gens G;
E4 = rsort flatten entries basis (4,E);
E2 = sort flatten entries basis (2,E);
B4 = sum ( for i from 0 to #Plucker-1 list leadCoefficient(E4#i*E2#i)*Plucker#i*E4#i);

-- Generators in B^{(1)}_{4,5}
d045 = G_14*e_0 - G_10*e_4 + G_6*e_5
d145 = G_14*e_1 - G_11*e_4 + G_7*e_5
d245 = G_14*e_2 - G_12*e_4 + G_8*e_5
d345 = G_14*e_3 - G_13*e_4 + G_9*e_5

h1 = {};
h2 = {};
m0B4 = m0(B4);
h2 = h2 | for t in terms(m0B4*(m2(d145)-m1(d045))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B4*(m2(d245)-m1(d145))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B4*(m1(d345))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B4*(m2(d345))) list leadCoefficient(t);

h = rsort(h1 | h2);
#h

H = ideal(h);
Hilb = trim (H + IG);

-- Action of PGL(3) over the projective plane
R = KK[x_2,x_1,x_0];
basisR2 = rsort flatten entries basis(2,R);
basisE2 = rsort flatten entries basis (2,E);
simpleChangesOfCoordinates = {matrix{{1,0,0},{0,1,0},{0,0,-1}}**KK, matrix{{1,0,0},{0,-1,0},{0,0,-1}}**KK, 
                              matrix{{0,1,0},{1,0,0},{0,0,1}}**KK, matrix{{0,0,1},{0,1,0},{1,0,0}}**KK,  matrix{{1,0,0},{0,0,1},{0,1,0}}**KK,
                              matrix{{1,1,0},{0,1,0},{0,0,1}}**KK, matrix{{1,0,1},{0,1,0},{0,0,1}}**KK,  matrix{{1,0,0},{0,1,1},{0,0,1}}**KK}

nEq = numgens Hilb;

-- Simple changes of coordinates
for mat in simpleChangesOfCoordinates do ( 
   print(mat);
   gg = map(R,R,flatten entries (vars(R)*(transpose (mat))));
   actionOverE = for t in basisR2 list gg(t);
   matE = matrix for t in actionOverE list for tt in basisR2 list leadCoefficient(t//tt);
   ggg = map(E,E,flatten entries (vars(E)*(transpose matE)));
   gB4 = ggg(B4);
   actionOverG = for e in basisE2 list leadCoefficient(gB4*e);
   matG = matrix for t in actionOverG list for v in gens(G) list leadCoefficient(t//v);
   gggg = map(G,G,flatten entries (vars(G)*(transpose matG)));
   Hilb = trim (Hilb + gggg(H));
   print("New equations: " | toString(numgens Hilb - nEq) | "\n");
   nEq = numgens Hilb;
);

gbH2 = gb (Hilb,DegreeLimit=>2);
Hilb = ideal(gens gbH2);
nEq = numgens Hilb;

-- Random change of coordinates
nRandomChangeCoordinates = 0;
isPGLinvariant = false;
while not isPGLinvariant do ( 
   randomMat = random(KK^3,KK^3);
   print(randomMat);
   gg = map(R,R,flatten entries (vars(R)*(transpose randomMat)));
   actionOverE = for t in basisR2 list gg(t);
   matE = matrix for t in actionOverE list for tt in basisR2 list leadCoefficient(t//tt);
   ggg = map(E,E,flatten entries (vars(E)*(transpose matE)));
   gB4 = ggg(B4);
   actionOverG = for e in basisE2 list leadCoefficient(gB4*e);
   matG = matrix for t in actionOverG list for v in gens(G) list leadCoefficient(t//v);
   gggg = map(G,G,flatten entries (vars(G)*(transpose matG)));
   newEq = for eq in h list (gggg(eq))%gbH2;
   Hilb = Hilb + ideal(gens gb (ideal newEq,DegreeLimit=>2)); 
   gbH2 = gb(Hilb,DegreeLimit=>2); 
   Hilb = ideal(gens gbH2); 
   print("New equations: " | toString(numgens Hilb - nEq) | "\n");
   if numgens Hilb == nEq then 
   (
     isPGLinvariant = true;
   ) 
   else 
   (
      nEq = numgens Hilb;
      nRandomChangeCoordinates = nRandomChangeCoordinates+1;
   );
);

nEq, numgens IG, nRandomChangeCoordinates
hilbertPolynomial(Hilb,Projective=>false)


-----------------------------------------------------
--        Hilbert scheme of 2 points in P^3        --
-----------------------------------------------------
restart
KK = ZZ/10007;
IG = Grassmannian(1,9,CoefficientRing=>KK,Variable=>D);
G = ring(IG);

-- Exterior algebra of polynomials of degree 2 in 4 variables
E = G[e_0..e_9,SkewCommutative=>true];

-- Exterior algebra of polynomials of degree 3 in 4 variables
F = G[f_0..f_19,SkewCommutative=>true];

-- Multiplication maps
m3 = map(F,E,{f_0,f_1,f_2,f_4,f_5,f_7,f_10,f_11,f_13,f_16});
m2 = map(F,E,{f_1,f_2,f_3,f_5,f_6,f_8,f_11,f_12,f_14,f_17});
m1 = map(F,E,{f_4,f_5,f_6,f_7,f_8,f_9,f_13,f_14,f_15,f_18});
m0 = map(F,E,{f_10,f_11,f_12,f_13,f_14,f_15,f_16,f_17,f_18,f_19});

-- Generator of the 8-th exterior power of the homogeneous piece of degree 2 of the ideal
Plucker = sort gens G;
E8 = rsort flatten entries basis (8,E);
E2 = sort flatten entries basis (2,E);
B8 = sum ( for i from 0 to #Plucker-1 list leadCoefficient(E8#i*E2#i)*Plucker#i*E8#i);

-- Generators in B^{(1)}_{8,9}
d089 = G_44*e_0 - G_36*e_8 + G_28*e_9;
d189 = G_44*e_1 - G_37*e_8 + G_29*e_9;
d289 = G_44*e_2 - G_38*e_8 + G_30*e_9;
d389 = G_44*e_3 - G_39*e_8 + G_31*e_9;
d489 = G_44*e_4 - G_40*e_8 + G_32*e_9;
d589 = G_44*e_5 - G_41*e_8 + G_33*e_9;
d689 = G_44*e_6 - G_42*e_8 + G_34*e_9;
d789 = G_44*e_7 - G_43*e_8 + G_35*e_9;

h1 = {};
h2 = {};
m0B8 = m0(B8);

h2 = h2 | for t in terms(m0B8*( m3(d189)-m2(d089) )) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B8*( m3(d289)-m2(d189) )) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B8*( m3(d389)-m1(d089) )) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B8*( m2(d389)-m1(d189) )) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B8*( m3(d489)-m1(d189) )) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B8*( m2(d489)-m1(d289) )) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B8*( m3(d589)-m1(d389) )) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B8*( m2(d589)-m1(d489) )) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B8*(m1(d689))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B8*(m2(d689))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B8*(m3(d689))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B8*(m1(d789))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B8*(m2(d789))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B8*(m3(d789))) list leadCoefficient(t);

h = rsort(h1 | h2);
#h

H = ideal(h);
Hilb = trim (H + IG);

-- Action of PGL(4) over the projective space
R = KK[x_3,x_2,x_1,x_0];
basisR2 = rsort flatten entries basis(2,R);
basisE2 = rsort flatten entries basis (2,E);
simpleChangesOfCoordinates = {matrix{{1,0,0,0},{0,1,0,0},{0,0,1,0},{0,0,0,-1}}**KK,
                              matrix{{1,0,0,0},{0,1,0,0},{0,0,-1,0},{0,0,0,-1}}**KK, matrix{{1,0,0,0},{0,-1,0,0},{0,0,-1,0},{0,0,0,-1}}**KK,
	                      matrix{{0,1,0,0},{1,0,0,0},{0,0,1,0},{0,0,0,1}}**KK, matrix{{0,0,1,0},{0,1,0,0},{1,0,0,0},{0,0,0,1}}**KK,
			      matrix{{0,0,0,1},{0,1,0,0},{0,0,1,0},{1,0,0,0}}**KK, matrix{{1,0,0,0},{0,0,1,0},{0,1,0,0},{0,0,0,1}}**KK,
			      matrix{{1,0,0,0},{0,0,0,1},{0,0,1,0},{0,1,0,0}}**KK, matrix{{1,0,0,0},{0,1,0,0},{0,0,0,1},{0,0,1,0}}**KK,
			      matrix{{1,1,0,0},{0,1,0,0},{0,0,1,0},{0,0,0,1}}**KK, matrix{{1,0,1,0},{0,1,0,0},{0,0,1,0},{0,0,0,1}}**KK,
			      matrix{{1,0,0,1},{0,1,0,0},{0,0,1,0},{0,0,0,1}}**KK, matrix{{1,0,0,0},{0,1,1,0},{0,0,1,0},{0,0,0,1}}**KK,
			      matrix{{1,0,0,0},{0,1,0,1},{0,0,1,0},{0,0,0,1}}**KK, matrix{{1,0,0,0},{0,1,0,0},{0,0,1,1},{0,0,0,1}}**KK}

nEq = numgens Hilb;

-- Simple changes of coordinates
for mat in simpleChangesOfCoordinates do ( 
   print(mat);
   gg = map(R,R,flatten entries (vars(R)*(transpose (mat))));
   actionOverE = for t in basisR2 list gg(t);
   matE = matrix for t in actionOverE list for tt in basisR2 list leadCoefficient(t//tt);
   ggg = map(E,E,flatten entries (vars(E)*(transpose matE)));
   gB8 = ggg(B8);
   actionOverG = for e in basisE2 list leadCoefficient(gB8*e);
   matG = matrix for t in actionOverG list for v in gens(G) list leadCoefficient(t//v);
   gggg = map(G,G,flatten entries (vars(G)*(transpose matG)));
   Hilb = trim (Hilb + gggg(H));
   print("New equations: " | toString(numgens Hilb - nEq) | "\n");
   nEq = numgens Hilb;
);

gbH2 = gb (Hilb,DegreeLimit=>2);
Hilb = ideal(gens gbH2);
nEq = numgens Hilb;

-- Random change of coordinates
nRandomChangeCoordinates = 0;
isPGLinvariant = false;
while not isPGLinvariant do ( 
   randomMat = random(KK^4,KK^4);
   print(randomMat);
   gg = map(R,R,flatten entries (vars(R)*(transpose randomMat)));
   actionOverE = for t in basisR2 list gg(t);
   matE = matrix for t in actionOverE list for tt in basisR2 list leadCoefficient(t//tt);
   ggg = map(E,E,flatten entries (vars(E)*(transpose matE)));
   gB8 = ggg(B8);
   actionOverG = for e in basisE2 list leadCoefficient(gB8*e);
   matG = matrix for t in actionOverG list for v in gens(G) list leadCoefficient(t//v);
   gggg = map(G,G,flatten entries (vars(G)*(transpose matG)));
   newEq = for eq in h list (gggg(eq))%gbH2;
   Hilb = Hilb + ideal(gens gb (ideal newEq,DegreeLimit=>2)); 
   gbH2 = gb(Hilb,DegreeLimit=>2); 
   Hilb = ideal(gens gbH2); 
   print("New equations: " | toString(numgens Hilb - nEq) | "\n");
   if numgens Hilb == nEq then 
   (
     isPGLinvariant = true;
   ) 
   else 
   (
      nEq = numgens Hilb;
      nRandomChangeCoordinates = nRandomChangeCoordinates+1;
   );
);

nEq, numgens IG, nRandomChangeCoordinates
hilbertPolynomial(Hilb,Projective=>false)
Hilb == saturate Hilb


-----------------------------------------------------
--        Hilbert scheme of 2 points in P^4        --
-----------------------------------------------------
restart
KK = ZZ/10007;
IG = Grassmannian(1,14,CoefficientRing=>KK,Variable=>D);
G = ring(IG);

-- Exterior algebra of polynomials of degree 2 in 5 variables
E = G[e_0..e_14,SkewCommutative=>true];

-- Exterior algebra of polynomials of degree 3 in 5 variables
F = G[f_0..f_34,SkewCommutative=>true];

-- Multiplication maps
m4 = map(F,E,{f_0,f_1,f_2,f_4,f_5,f_7,f_10,f_11,f_13,f_16,f_20,f_21,f_23,f_26,f_30});
m3 = map(F,E,{f_1,f_2,f_3,f_5,f_6,f_8,f_11,f_12,f_14,f_17,f_21,f_22,f_24,f_27,f_31});
m2 = map(F,E,{f_4,f_5,f_6,f_7,f_8,f_9,f_13,f_14,f_15,f_18,f_23,f_24,f_25,f_28,f_32});
m1 = map(F,E,{f_10,f_11,f_12,f_13,f_14,f_15,f_16,f_17,f_18,f_19,f_26,f_27,f_28,f_29,f_33});
m0 = map(F,E,{f_20,f_21,f_22,f_23,f_24,f_25,f_26,f_27,f_28,f_29,f_30,f_31,f_32,f_33,f_34});

-- Generator of the 13-th exterior power of the homogeneous piece of degree 2 of the ideal
Plucker = sort gens G;
E13 = rsort flatten entries basis (13,E);
E2 = sort flatten entries basis (2,E);
B13 = sum ( for i from 0 to #Plucker-1 list leadCoefficient(E13#i*E2#i)*Plucker#i*E13#i);

-- Generators in B^{(1)}_{13,14} and equations
h1 = {};
h2 = {};
m0B13 = m0(B13);

d01314 = G_104*e_0 - G_91*e_13 + G_78*e_14;

d11314 = G_104*e_1 - G_92*e_13 + G_79*e_14;
h2 = h2 | for t in terms(m0B13*(m4(d11314)-m3(d01314))) list leadCoefficient(t);

d21314 = G_104*e_2 - G_93*e_13 + G_80*e_14;
h2 = h2 | for t in terms(m0B13*(m4(d21314)-m3(d11314))) list leadCoefficient(t);

d31314 = G_104*e_3 - G_94*e_13 + G_81*e_14;
h2 = h2 | for t in terms(m0B13*(m4(d31314)-m2(d01314))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B13*(m3(d31314)-m2(d11314))) list leadCoefficient(t);

d41314 = G_104*e_4 - G_95*e_13 + G_82*e_14;
h2 = h2 | for t in terms(m0B13*(m4(d41314)-m2(d11314))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B13*(m3(d41314)-m2(d21314))) list leadCoefficient(t);

d51314 = G_104*e_5 - G_96*e_13 + G_83*e_14;
h2 = h2 | for t in terms(m0B13*(m4(d51314)-m2(d31314))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B13*(m3(d51314)-m2(d41314))) list leadCoefficient(t);

d61314 = G_104*e_6 - G_97*e_13 + G_84*e_14;
h2 = h2 | for t in terms(m0B13*(m4(d61314)-m1(d01314))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B13*(m3(d61314)-m1(d11314))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B13*(m2(d61314)-m1(d31314))) list leadCoefficient(t);

d71314 = G_104*e_7 - G_98*e_13 + G_85*e_14;
h2 = h2 | for t in terms(m0B13*(m4(d71314)-m1(d11314))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B13*(m3(d71314)-m1(d21314))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B13*(m2(d71314)-m1(d41314))) list leadCoefficient(t);

d81314 = G_104*e_8 - G_99*e_13 + G_86*e_14;
h2 = h2 | for t in terms(m0B13*(m4(d81314)-m1(d31314))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B13*(m3(d81314)-m1(d41314))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B13*(m2(d81314)-m1(d51314))) list leadCoefficient(t);

d91314 = G_104*e_9 - G_100*e_13 + G_87*e_14;
h2 = h2 | for t in terms(m0B13*(m4(d91314)-m1(d61314))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B13*(m3(d91314)-m1(d71314))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B13*(m2(d91314)-m1(d81314))) list leadCoefficient(t);

d101314 = G_104*e_10 - G_101*e_13 + G_88*e_14;
h2 = h2 | for t in terms(m0B13*(m1(d101314))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B13*(m2(d101314))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B13*(m3(d101314))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B13*(m4(d101314))) list leadCoefficient(t);

d111314 = G_104*e_11 - G_102*e_13 + G_89*e_14;
h2 = h2 | for t in terms(m0B13*(m1(d111314))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B13*(m2(d111314))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B13*(m3(d111314))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B13*(m4(d111314))) list leadCoefficient(t);

d121314 = G_104*e_12 - G_103*e_13 + G_90*e_14;
h2 = h2 | for t in terms(m0B13*(m1(d121314))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B13*(m2(d121314))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B13*(m3(d121314))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B13*(m4(d121314))) list leadCoefficient(t);


h = rsort (h1 | h2);
#h

H = ideal(h);
Hilb = trim (H + IG);

-- Action of PGL(5) over P^4
R = KK[x_4,x_3,x_2,x_1,x_0];
basisR2 = rsort flatten entries basis(2,R);
basisE2 = rsort flatten entries basis (2,E);
simpleChangesOfCoordinates = {matrix{{1,0,0,0,0},{0,1,0,0,0},{0,0,1,0,0},{0,0,0,1,0},{0,0,0,0,-1}}**KK,
                matrix{{1,0,0,0,0},{0,1,0,0,0},{0,0,1,0,0},{0,0,0,-1,0},{0,0,0,0,-1}}**KK, matrix{{1,0,0,0,0},{0,1,0,0,0},{0,0,-1,0,0},{0,0,0,-1,0},{0,0,0,0,-1}}**KK,
		matrix{{1,0,0,0,0},{0,-1,0,0,0},{0,0,-1,0,0},{0,0,0,-1,0},{0,0,0,0,-1}}**KK, matrix{{0,1,0,0,0},{1,0,0,0,0},{0,0,1,0,0},{0,0,0,1,0},{0,0,0,0,1}}**KK,
		matrix{{0,0,1,0,0},{0,1,0,0,0},{1,0,0,0,0},{0,0,0,1,0},{0,0,0,0,1}}**KK, matrix{{0,0,0,1,0},{0,1,0,0,0},{0,0,1,0,0},{1,0,0,0,0},{0,0,0,0,1}}**KK,
		matrix{{0,0,0,0,1},{0,1,0,0,0},{0,0,1,0,0},{0,0,0,1,0},{1,0,0,0,0}}**KK, matrix{{1,0,0,0,0},{0,0,1,0,0},{0,1,0,0,0},{0,0,0,1,0},{0,0,0,0,1}}**KK,
		matrix{{1,0,0,0,0},{0,0,0,1,0},{0,0,1,0,0},{0,1,0,0,0},{0,0,0,0,1}}**KK, matrix{{1,0,0,0,0},{0,0,0,0,1},{0,0,1,0,0},{0,0,0,1,0},{0,1,0,0,0}}**KK,
		matrix{{1,0,0,0,0},{0,1,0,0,0},{0,0,0,1,0},{0,0,1,0,0},{0,0,0,0,1}}**KK, matrix{{1,0,0,0,0},{0,1,0,0,0},{0,0,0,0,1},{0,0,0,1,0},{0,0,1,0,0}}**KK,
		matrix{{1,0,0,0,0},{0,1,0,0,0},{0,0,1,0,0},{0,0,0,0,1},{0,0,0,1,0}}**KK, matrix{{1,1,0,0,0},{0,1,0,0,0},{0,0,1,0,0},{0,0,0,1,0},{0,0,0,0,1}}**KK,
		matrix{{1,0,1,0,0},{0,1,0,0,0},{0,0,1,0,0},{0,0,0,1,0},{0,0,0,0,1}}**KK, matrix{{1,0,0,1,0},{0,1,0,0,0},{0,0,1,0,0},{0,0,0,1,0},{0,0,0,0,1}}**KK,
		matrix{{1,0,0,0,1},{0,1,0,0,0},{0,0,1,0,0},{0,0,0,1,0},{0,0,0,0,1}}**KK, matrix{{1,0,0,0,0},{0,1,1,0,0},{0,0,1,0,0},{0,0,0,1,0},{0,0,0,0,1}}**KK,
		matrix{{1,0,0,0,0},{0,1,0,1,0},{0,0,1,0,0},{0,0,0,1,0},{0,0,0,0,1}}**KK, matrix{{1,0,0,0,0},{0,1,0,0,1},{0,0,1,0,0},{0,0,0,1,0},{0,0,0,0,1}}**KK,
		matrix{{1,0,0,0,0},{0,1,0,0,0},{0,0,1,1,0},{0,0,0,1,0},{0,0,0,0,1}}**KK, matrix{{1,0,0,0,0},{0,1,0,0,0},{0,0,1,0,1},{0,0,0,1,0},{0,0,0,0,1}}**KK,
		matrix{{1,0,0,0,0},{0,1,0,0,0},{0,0,1,0,0},{0,0,0,1,1},{0,0,0,0,1}}**KK}


-- Simple changes of coordinates
for mat in simpleChangesOfCoordinates do ( 
   print(mat);
   gg = map(R,R,flatten entries (vars(R)*(transpose (mat))));
   actionOverE = for t in basisR2 list gg(t);
   matE = matrix for t in actionOverE list for tt in basisR2 list leadCoefficient(t//tt);
   ggg = map(E,E,flatten entries (vars(E)*(transpose matE)));
   gB13 = ggg(B13);
   actionOverG = for e in basisE2 list leadCoefficient(gB13*e);
   matG = matrix for t in actionOverG list for v in gens(G) list leadCoefficient(t//v);
   gggg = map(G,G,flatten entries (vars(G)*(transpose matG)));
   Hilb = trim (Hilb + gggg(H));
   print("New equations: " | toString(numgens Hilb - nEq) | "\n");
   nEq = numgens Hilb;
);

gbH2 = gb (Hilb,DegreeLimit=>2);
Hilb = ideal(gens gbH2);
nEq = numgens Hilb;

-- Random change of coordinates
nRandomChangeCoordinates = 0;
isPGLinvariant = false;
while not isPGLinvariant do ( 
   randomMat = random(KK^5,KK^5);
   print(randomMat);
   gg = map(R,R,flatten entries (vars(R)*(transpose randomMat)));
   actionOverE = for t in basisR2 list gg(t);
   matE = matrix for t in actionOverE list for tt in basisR2 list leadCoefficient(t//tt);
   ggg = map(E,E,flatten entries (vars(E)*(transpose matE)));
   gB13 = ggg(B13);
   actionOverG = for e in basisE2 list leadCoefficient(gB13*e);
   matG = matrix for t in actionOverG list for v in gens(G) list leadCoefficient(t//v);
   gggg = map(G,G,flatten entries (vars(G)*(transpose matG)));
   newEq = for eq in h list (gggg(h))%gbH2;
   Hilb = Hilb + ideal(gens gb (ideal newEq,DegreeLimit=>2)); 
   gbH2 = gb(Hilb,DegreeLimit=>2); 
   Hilb = ideal(gens gbH2); 
   print("New equations: " | toString(numgens Hilb - nEq) | "\n");
   if numgens Hilb == nEq then 
   (
     isPGLinvariant = true;
   ) 
   else 
   (
      nEq = numgens Hilb;
      nRandomChangeCoordinates = nRandomChangeCoordinates+1;
   );
);

nEq, numgens IG, nRandomChangeCoordinates
hilbertPolynomial(Hilb,Projective=>false)


-----------------------------------------------------
--        Hilbert scheme of 3 points in P^2        --
-----------------------------------------------------
restart
KK = ZZ/10007;
IG = Grassmannian(2,9,CoefficientRing=>KK,Variable=>D);
G = ring(IG);

-- Exterior algebra of polynomials of degree 3 in 3 variables
E = G[e_0..e_9,SkewCommutative=>true];

-- Exterior algebra of polynomials of degree 4 in 3 variables 
F = G[f_0..f_14,SkewCommutative=>true];

-- Multiplication maps
m2 = map(F,E,{f_0,f_1,f_2,f_3,f_5,f_6,f_7,f_9,f_10,f_12});
m1 = map(F,E,{f_1,f_2,f_3,f_4,f_6,f_7,f_8,f_10,f_11,f_13});
m0 = map(F,E,{f_5,f_6,f_7,f_8,f_9,f_10,f_11,f_12,f_13,f_14});


-- Generator of the seventh exterior power of the homogeneous piece of degree 3 of the ideal
Plucker = sort gens G;
E7 = rsort flatten entries basis (7,E);
E3 = sort flatten entries basis (3,E);
B7 = sum ( for i from 0 to #Plucker-1 list leadCoefficient(E7#i*E3#i)*Plucker#i*E7#i);

-- Generators in B^{(1)}_{6,8,9} U B^{(1)}_{7,8,9} and equations
h1 = {};
h2 = {};
m0B7 = m0(B7);

d0689 = -G_118*e_0 + G_112*e_6 - G_99*e_8  + G_71*e_9;
d1689 = -G_118*e_1 + G_113*e_6 - G_100*e_8  + G_72*e_9;
d2689 = -G_118*e_2 + G_114*e_6 - G_101*e_8  + G_73*e_9;
d3689 = -G_118*e_3 + G_115*e_6 - G_102*e_8  + G_74*e_9;
h2 = h2 | for t in terms(m0B7*(m1(d0689)-m2(d1689))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B7*(m1(d1689)-m2(d2689))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B7*(m1(d2689)-m2(d3689))) list leadCoefficient(t);

d0789 = -G_119*e_0 + G_112*e_7 - G_105*e_8 + G_77*e_9;
d1789 = -G_119*e_1 + G_113*e_7 - G_106*e_8 + G_78*e_9;
d2789 = -G_119*e_2 + G_114*e_7 - G_107*e_8 + G_79*e_9;
d3789 = -G_119*e_3 + G_115*e_7 - G_108*e_8 + G_80*e_9;
h2 = h2 | for t in terms(m0B7*(m1(d0789)-m2(d1789))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B7*(m1(d1789)-m2(d2789))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B7*(m1(d2789)-m2(d3789))) list leadCoefficient(t);

d4689 =  -G_118*e_4 + G_116*e_6 - G_103*e_8 + G_75*e_9;
h2 = h2 | for t in terms(m0B7*(m1(d4689))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B7*(m2(d4689))) list leadCoefficient(t);

d4789 =  -G_119*e_4 + G_116*e_7 - G_109*e_8 + G_81*e_9;
h2 = h2 | for t in terms(m0B7*(m1(d4789))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B7*(m2(d4789))) list leadCoefficient(t);

d5689 =  -G_118*e_5 + G_117*e_6 - G_104*e_8 + G_76*e_9;
h2 = h2 | for t in terms(m0B7*(m1(d5689))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B7*(m2(d5689))) list leadCoefficient(t);

d5789 =  -G_119*e_5 + G_117*e_7 - G_110*e_8 + G_82*e_9;
h2 = h2 | for t in terms(m0B7*(m1(d5789))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B7*(m2(d5789))) list leadCoefficient(t);

d6789 =  -G_119*e_6 + G_118*e_7 - G_111*e_8 + G_83*e_9;
h2 = h2 | for t in terms(m0B7*(m1(d6789))) list leadCoefficient(t);
h2 = h2 | for t in terms(m0B7*(m2(d6789))) list leadCoefficient(t);

h = rsort (h1 | h2);
#h

H = ideal(h);
Hilb = trim (H + IG);

-- Action of PGL(3) over the projective plane
R = KK[x_2,x_1,x_0];
basisR3 = rsort flatten entries basis(3,R);
basisE3 = rsort flatten entries basis (3,E);
simpleChangesOfCoordinates = {matrix{{1,0,0},{0,1,0},{0,0,-1}}**KK, matrix{{1,0,0},{0,-1,0},{0,0,-1}}**KK, 
                              matrix{{0,1,0},{1,0,0},{0,0,1}}**KK, matrix{{0,0,1},{0,1,0},{1,0,0}}**KK,  matrix{{1,0,0},{0,0,1},{0,1,0}}**KK,
                              matrix{{1,1,0},{0,1,0},{0,0,1}}**KK, matrix{{1,0,1},{0,1,0},{0,0,1}}**KK,  matrix{{1,0,0},{0,1,1},{0,0,1}}**KK}

nEq = numgens Hilb;

-- Simple changes of coordinates
for mat in simpleChangesOfCoordinates do ( 
   print(mat);
   gg = map(R,R,flatten entries (vars(R)*(transpose (mat))));
   actionOverE = for t in basisR3 list gg(t);
   matE = matrix for t in actionOverE list for tt in basisR3 list leadCoefficient(t//tt);
   ggg = map(E,E,flatten entries (vars(E)*(transpose matE)));
   gB7 = ggg(B7);
   actionOverG = for e in basisE2 list leadCoefficient(gB7*e);
   matG = matrix for t in actionOverG list for v in gens(G) list leadCoefficient(t//v);
   gggg = map(G,G,flatten entries (vars(G)*(transpose matG)));
   Hilb = trim (Hilb + gggg(H));
   print("New equations: " | toString(numgens Hilb - nEq) | "\n");
   nEq = numgens Hilb;
);

gbH2 = gb (Hilb,DegreeLimit=>2);
Hilb = ideal(gens gbH2);
nEq = numgens Hilb;

-- Random change of coordinates
nRandomChangeCoordinates = 0;
isPGLinvariant = false;
while not isPGLinvariant do ( 
   randomMat = random(KK^3,KK^3);
   print(randomMat);
   gg = map(R,R,flatten entries (vars(R)*(transpose randomMat)));
   actionOverE = for t in basisR3 list gg(t);
   matE = matrix for t in actionOverE list for tt in basisR3 list leadCoefficient(t//tt);
   ggg = map(E,E,flatten entries (vars(E)*(transpose matE)));
   gB7 = ggg(B7);
   actionOverG = for e in basisE2 list leadCoefficient(gB7*e);
   matG = matrix for t in actionOverG list for v in gens(G) list leadCoefficient(t//v);
   gggg = map(G,G,flatten entries (vars(G)*(transpose matG)));
   newEq = for eq in h list (gggg(h))%gbH2;
   Hilb = Hilb + ideal(gens gb (ideal newEq,DegreeLimit=>2)); 
   gbH2 = gb(Hilb,DegreeLimit=>2); 
   Hilb = ideal(gens gbH2); 
   print("New equations: " | toString(numgens Hilb - nEq) | "\n");
   if numgens Hilb == nEq then 
   (
     isPGLinvariant = true;
   ) 
   else 
   (
      nEq = numgens Hilb;
      nRandomChangeCoordinates = nRandomChangeCoordinates+1;
   );
);

nEq, numgens IG, nRandomChangeCoordinates
hilbertPolynomial(Hilb,Projective=>false)
