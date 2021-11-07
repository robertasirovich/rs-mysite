--------------------------------------------------------------------------------
----  Example 1.3 - pag. 7                                                  ----
--------------------------------------------------------------------------------
restart
loadPackage("GroebnerFanHilbertScheme");
R = QQ[x_2,x_1,x_0];
compareBorel(x_0*x_2^2,x_0^2*x_1) > 0
compareBorel(x_0*x_2^2,x_1^3) === null


--------------------------------------------------------------------------------
----  Example 1.5 - pag. 8                                                  ----
--------------------------------------------------------------------------------
restart
loadPackage("StronglyStableIdeals");
loadPackage("GroebnerFanHilbertScheme");
R = QQ[x_2,x_1,x_0];
hp = 3*projectiveHilbertPolynomial 0;
S = stronglyStableIdeals(hp,R);
L = S#0, J = S#1
r = gotzmannNumber hp

Lfrak = flatten entries gens truncate(r,L)
Lfrak2 = select(Lfrak, m -> (minVar m) == x_2)
Lfrak1 = select(Lfrak, m -> (minVar m) == x_1)
Lfrak0 = select(Lfrak, m -> (minVar m) == x_0)

Jfrak = flatten entries gens truncate(r,J)
Jfrak2 = select(Jfrak, m -> (minVar m) == x_2)
Jfrak1 = select(Jfrak, m -> (minVar m) == x_1)
Jfrak0 = select(Jfrak, m -> (minVar m) == x_0)

Lfrak2 == Jfrak2, Lfrak1 == Jfrak1, Lfrak0 == Jfrak0


--------------------------------------------------------------------------------
----  Example 2.2 - pag. 10                                                  ----
--------------------------------------------------------------------------------
-- BA1
restart
R = QQ[x_2,x_1,x_0];
r = 3;
L = ideal(x_2,x_1^3);
J = ideal(x_2^2,x_1*x_2,x_1^2)
Lfrak = flatten entries gens truncate(r,L);
Jfrak = flatten entries gens truncate(r,J);
LsetminusJ = select(Lfrak, m -> not member(m,Jfrak))
JsetminusL = select(Jfrak, m -> not member(m,Lfrak))

-- BA2
restart
loadPackage("GroebnerFanHilbertScheme");
R = QQ[x_2,x_1,x_0];
r = 5;
L = ideal(x_2,x_1^5)
J = ideal(x_2^2,x_1^2*x_2,x_1^3)
Lfrak = flatten entries gens truncate(r,L);
Jfrak = flatten entries gens truncate(r,J);
LsetminusJ = rsort select(Lfrak, m -> not member(m,Jfrak))
JsetminusL = rsort select(Jfrak, m -> not member(m,Lfrak))

for m in LsetminusJ list compareBorel(first LsetminusJ,m)
for m in JsetminusL list compareBorel(first JsetminusL,m)

movesLsetminusJ = for m in LsetminusJ list m/(first LsetminusJ)
movesJsetminusL = for m in JsetminusL list m/(first JsetminusL)
movesLsetminusJ == movesJsetminusL

-- BA3
restart
loadPackage("GroebnerFanHilbertScheme");
R = QQ[x_3,x_2,x_1,x_0];
r = 4;
J = ideal(x_3^2,x_2*x_3,x_2^2)
K = ideal(x_3^2,x_2*x_3,x_1*x_3,x_2^3)
Jfrak = flatten entries gens truncate(r,J);
Kfrak = flatten entries gens truncate(r,K);

JsetminusK = rsort select(Jfrak, m -> not member(m,Kfrak))
KsetminusJ = rsort select(Kfrak, m -> not member(m,Jfrak))

for m in JsetminusK list compareBorel(first JsetminusK,m)
for m in KsetminusJ list compareBorel(first KsetminusJ,m)

movesJsetminusK = for m in JsetminusK list m/(first JsetminusK)
movesKsetminusJ = for m in KsetminusJ list m/(first KsetminusJ)
movesJsetminusK == movesKsetminusJ


--------------------------------------------------------------------------------
----  Example 2.3 - pag. 11                                                  ----
--------------------------------------------------------------------------------
-- nBA1
restart
loadPackage("GroebnerFanHilbertScheme");
R = QQ[x_2,x_1,x_0];
r = 8;
J = ideal(x_2^2,x_1^2*x_2,x_1^6)
K = ideal(x_2^3,x_1*x_2^2,x_1^3*x_2,x_1^4)
Jfrak = flatten entries gens truncate(r,J);
Kfrak = flatten entries gens truncate(r,K);
JsetminusK = rsort select(Jfrak, m -> not member(m,Kfrak))
KsetminusJ = rsort select(Kfrak, m -> not member(m,Jfrak))

for m in JsetminusK list compareBorel(first JsetminusK,m)
compareBorel(JsetminusK#0,JsetminusK#1) == null

-- nBA2
restart
loadPackage("GroebnerFanHilbertScheme");
R = QQ[x_2,x_1,x_0];
r = 6;
J = ideal(x_2^2,x_1*x_2,x_1^5)
K = ideal(x_2^3,x_1*x_2^2,x_1^2*x_2,x_1^3)
Jfrak = flatten entries gens truncate(r,J);
Kfrak = flatten entries gens truncate(r,K);
JsetminusK = rsort select(Jfrak, m -> not member(m,Kfrak))
KsetminusJ = rsort select(Kfrak, m -> not member(m,Jfrak))

for m in JsetminusK list compareBorel(first JsetminusK,m)
for m in KsetminusJ list compareBorel(first KsetminusJ,m)

movesJsetminusK = for m in JsetminusK list m/(first JsetminusK)
movesKsetminusJ = for m in KsetminusJ list m/(first KsetminusJ)
movesJsetminusK == movesKsetminusJ

-- nBA3
restart
loadPackage("GroebnerFanHilbertScheme");
R = QQ[x_3,x_2,x_1,x_0];
r = 4;
L = ideal(x_3,x_2^4,x_1*x_2^3)
J = ideal(x_3^2,x_2*x_3,x_2^2)
Lfrak = flatten entries gens truncate(r,L);
Jfrak = flatten entries gens truncate(r,J);

LsetminusJ = rsort select(Lfrak, m -> not member(m,Jfrak))
JsetminusL = rsort select(Jfrak, m -> not member(m,Lfrak))

for m in LsetminusJ list compareBorel(first LsetminusJ,m)
for m in JsetminusL list compareBorel(first JsetminusL,m)


--------------------------------------------------------------------------------
----  Example 2.7 - pag. 14                                                 ----
--------------------------------------------------------------------------------
restart
R = QQ[x_3,x_2,x_1,x_0];
r = 4;
J = ideal(x_3^2,x_2*x_3,x_2^2)
K = ideal(x_3^2,x_2*x_3,x_1*x_3,x_2^3)
Jfrak = flatten entries gens truncate(r,J);
Kfrak = flatten entries gens truncate(r,K);

JsetminusK = rsort select(Jfrak, m -> not member(m,Kfrak))
KsetminusJ = rsort select(Kfrak, m -> not member(m,Jfrak))
JcapK = select(Jfrak, m -> member(m,Kfrak))

RY = QQ[y_0,y_1][gens R];
monomialPart = for m in JcapK list sub(m,RY);
binomialPart = for i from 0 to #JsetminusK-1 list y_0*sub(JsetminusK#i,RY) + y_1*sub(KsetminusJ#i,RY)
borelDeformation = ideal(monomialPart | binomialPart);
syz gens borelDeformation

RT = QQ[T][gens RY];
U0 = map(RT,RY,gens RT | {1,T})
affDef0 = U0 borelDeformation
syz gens affDef0

U1 = map(RT,RY,gens RT | {T,1})
affDef1 = U1 borelDeformation
syz gens affDef1


--------------------------------------------------------------------------------
----  Example 2.10 - pag. 15                                                ----
--------------------------------------------------------------------------------
restart
R = QQ[x_2,x_1,x_0];
r = 3;
L = ideal(x_2,x_1^3);
J = ideal(x_2^2,x_1*x_2,x_1^2)
Lfrak = flatten entries gens truncate(r,L);
Jfrak = flatten entries gens truncate(r,J);
LsetminusJ = select(Lfrak, m -> not member(m,Jfrak))
JsetminusL = select(Jfrak, m -> not member(m,Lfrak))
LcapJ = select(Lfrak, m -> member(m,Jfrak))

RY = QQ[y_0,y_1][gens R];
monomialPart = rsort for m in LcapJ list sub(m,RY);
binomialPart =  {y_0*sub(JsetminusL#0,RY) + y_1*sub(LsetminusJ#0,RY)}
borelDeformation = ideal(monomialPart | binomialPart);
Br = rsort flatten entries basis(r,RY);
M = matrix for f in borelDeformation_* list for m in Br list leadCoefficient(f//m) 
Y = ring M;

P = QQ[Variables=>binomial(#Br,#Lfrak)];
minorIndices = subsets(10,7);
veroneseMap = map(Y,P,for s in minorIndices list det M_s);
line = kernel veroneseMap
degree line, genus line


--------------------------------------------------------------------------------
----  Example 3.2 - pag. 16  +  Figure 4  +  Figure 6                       ----
--------------------------------------------------------------------------------
-- (1)
restart
loadPackage("GroebnerFanHilbertScheme");
R = QQ[x_2,x_1,x_0];
hp = 5*projectiveHilbertPolynomial 0;
(V,E) = borelGraph(hp,R);
netList V
netList E

(V',E') = degenerationGraph(hp,R,MonomialOrder=>GLex);
netList E'

(V'',E'') = degenerationGraph(hp,R,{3,1,0});
netList E''

-- (2)
restart
loadPackage("GroebnerFanHilbertScheme");
R = QQ[x_3,x_2,x_1,x_0];
hp = 3*projectiveHilbertPolynomial 1 - 2*projectiveHilbertPolynomial 0;
(V,E) = borelGraph(hp,R);
netList V
netList E

(V',E') = degenerationGraph(hp,R,MonomialOrder=>GRevLex);
netList E'

(V'',E'') = degenerationGraph(hp,R,{3,2,1,0});
netList E''


--------------------------------------------------------------------------------
----  Example 3.6 - pag. 18                                                 ----
--------------------------------------------------------------------------------
restart
loadPackage("GroebnerFanHilbertScheme");
R = QQ[x_3,x_2,x_1,x_0];
hp = 5*projectiveHilbertPolynomial 1 - 7*projectiveHilbertPolynomial 0;

(V,E) = degenerationGraph(hp,R,MonomialOrder=>GRevLex);
netList V
netList E


--------------------------------------------------------------------------------
----  Example 3.12 - pag. 21  +  Figure 7                                   ----
--------------------------------------------------------------------------------
restart
loadPackage("Polyhedra",Reload=>true);
loadPackage("GroebnerFanHilbertScheme");
R = QQ[x_2,x_1,x_0];
hp = 5*projectiveHilbertPolynomial 0;
(V,E,F) = groebnerFan(hp,R);
netList V
netList E
extremalRays = rays F
maximalCones = maxCones F
extremalRaysMaximalCones = for mc in maximalCones list extremalRays_mc
netList for eRmC in extremalRaysMaximalCones list (degenerationGraph(V,E,sum entries transpose eRmC))#1

conesDim2 = cones(2,F)
extremalRaysConesDim2 = for mc in conesDim2 list extremalRays_mc
netList for eRmC in extremalRaysConesDim2 list (degenerationGraph(V,E,sum entries transpose eRmC))#1

conesDim1 = cones(1,F)
extremalRaysConesDim1 = for mc in conesDim1 list extremalRays_mc
netList for eRmC in extremalRaysConesDim1 list (degenerationGraph(V,E,sum entries transpose eRmC))#1


--------------------------------------------------------------------------------
----  Example 3.15 - pag. 24  +  Figure 8                                   ----
--------------------------------------------------------------------------------
restart
loadPackage("Polyhedra",Reload=>true);
loadPackage("GroebnerFanHilbertScheme");
R = QQ[x_3,x_2,x_1,x_0];
hp = 3*projectiveHilbertPolynomial 1 - 2*projectiveHilbertPolynomial 0;
(V,E,F) = groebnerFan(hp,R);
extremalRays = rays F;
maximalCones = for mc in maxCones F list coneFromVData extremalRays_mc;

MRevLex = matrix {{1,1,1,1},{0,0,0,-1},{0,0,-1,0},{0,-1,0,0}}
wRevLex = termOrder2weightOrder(E,MRevLex)
for C in maximalCones list contains(C, transpose matrix {wRevLex})

MDegLex = matrix {{1,1,1,1},{1,0,0,0},{0,1,0,0},{0,0,1,0}}
wDegLex = termOrder2weightOrder(E,MDegLex)
for C in maximalCones list contains(C, transpose matrix {wDegLex})


--------------------------------------------------------------------------------
----  Example 4.5 - pag. 28                                                 ----
--------------------------------------------------------------------------------
restart
loadPackage("GroebnerFanHilbertScheme");
loadPackage("StronglyStableIdeals");
R = QQ[x_3,x_2,x_1,x_0];
L = ideal(x_3^2,x_2*x_3,x_2^4)
hp = hilbertPolynomial(L,Projective=>false)
r = gotzmannNumber hp
isHilbSegment L

S = newRing(R,MonomialOrder=>{Weights=>{1,1,1,1},Weights=>{47,17,3,1}});
L = sub(L,S);
J = ideal(x_3^2,x_2^2*x_3,x_1*x_2*x_3,x_1^2*x_3,x_2^5)
hilbertPolynomial L == hilbertPolynomial J

Lfrak = rsort flatten entries gens truncate(r,L);
Jfrak = rsort flatten entries gens truncate(r,J);

-- Step 0
Afrak = select(Lfrak, m -> not member(m,Jfrak))
Bfrak = select(Jfrak, m -> not member(m,Lfrak))

-- Step 1
maxA = max Afrak
minB = min select(Bfrak, m -> minVar m == minVar maxA)

-- Step 2
eB = select(Jfrak, m -> compareBorel(minB,m) =!= null and  compareBorel(minB,m) >= 0)
movesB = for m in eB list m/minB
eA = for e in movesB list e*maxA -- failure

-- Step 3
Afrak = select(Afrak, m -> compareBorel(m,maxA) === null)

-- Step 1
maxA = max Afrak
minB = min select(Bfrak, m -> minVar m == minVar maxA)

-- Step 2
Ifrak = append(delete(minB,Jfrak),maxA);
I = saturate ideal Ifrak


--------------------------------------------------------------------------------
----  Example 4.7 - pag. 29  +  Figure 9                                    ----
--------------------------------------------------------------------------------
restart
loadPackage("StronglyStableIdeals");
loadPackage("GroebnerFanHilbertScheme");
R = QQ[x_3,x_2,x_1,x_0];
hp = 5*projectiveHilbertPolynomial 1 - 7*projectiveHilbertPolynomial 0;
(V,E) = borelGraph(hp,R);
netList V, netList E

isHilbSegment V#0
netList spanningTree(V,V#0,MonomialOrder=>{Weights=>{1,1,1,1},Weights=>{19,4,2,1}})

isHilbSegment V#1

isHilbSegment V#2
netList spanningTree(V,V#2,MonomialOrder=>{Weights=>{1,1,1,1},Weights=>{44,9,4,1}})

isHilbSegment V#3
netList spanningTree(V,V#3,MonomialOrder=>{Weights=>{1,1,1,1},Weights=>{53,12,4,1}})

isHilbSegment V#4
netList spanningTree(V,V#4,MonomialOrder=>{Weights=>{1,1,1,1},Weights=>{45,11,3,1}})

isHilbSegment V#5

isHilbSegment V#6
netList spanningTree(V,V#6,MonomialOrder=>{Weights=>{1,1,1,1},Weights=>{47,17,3,1}})


--------------------------------------------------------------------------------
----  Example 4.13 - pag. 33                                                ----
--------------------------------------------------------------------------------
-- (1) Figure 10(B)
restart
loadPackage("StronglyStableIdeals");
loadPackage("Polyhedra",Reload=>true);
loadPackage("GroebnerFanHilbertScheme");
R = QQ[x_3,x_2,x_1,x_0];
hp = 8*projectiveHilbertPolynomial 0;
(V,E,F) = groebnerFan(hp,R);
#V, #E
extremalRays = rays F;
conesMaxDim = for mc in maxCones F list coneFromVData extremalRays_mc;
#conesMaxDim, numColumns extremalRays

isHilbSegment V#0
cones0 = select(conesMaxDim, C -> first maximalElementsDegenerationGraph degenerationGraph(V,E,C) == V#0);
rays0 = for C in cones0 list rays C
allRays = first rays0;
for i from 1 to #cones0-1 do allRays = allRays | rays0#i;
C0 = rays coneFromVData allRays

isHilbSegment V#1
cones1 = select(conesMaxDim, C -> first maximalElementsDegenerationGraph degenerationGraph(V,E,C) == V#1);
rays1 = for C in cones1 list rays C
allRays = first rays1;
for i from 1 to #cones1-1 do allRays = allRays | rays1#i;
C1 = rays coneFromVData allRays

isHilbSegment V#2
cones2 = select(conesMaxDim, C -> first maximalElementsDegenerationGraph degenerationGraph(V,E,C) == V#2);
rays2 = for C in cones2 list rays C
allRays = first rays2;
for i from 1 to #cones2-1 do allRays = allRays | rays2#i;
C2 = rays coneFromVData allRays

isHilbSegment V#3
cones3 = select(conesMaxDim, C -> first maximalElementsDegenerationGraph degenerationGraph(V,E,C) == V#3);
rays3 = for C in cones3 list rays C
allRays = first rays3;
for i from 1 to #cones3-1 do allRays = allRays | rays3#i;
C3 = rays coneFromVData allRays

isHilbSegment V#4

isHilbSegment V#5
cones5 = select(conesMaxDim, C -> first maximalElementsDegenerationGraph degenerationGraph(V,E,C) == V#5);
rays5 = for C in cones1 list rays C
allRays = first rays5;
for i from 1 to #cones5-1 do allRays = allRays | rays5#i;
C5 = rays coneFromVData allRays

isHilbSegment V#6
cones6 = select(conesMaxDim, C -> first maximalElementsDegenerationGraph degenerationGraph(V,E,C) == V#6);
rays6 = for C in cones6 list rays C
allRays = first rays6;
for i from 1 to #cones6-1 do allRays = allRays | rays6#i;
C6 = rays coneFromVData allRays

isHilbSegment V#7
cones7 = select(conesMaxDim, C -> first maximalElementsDegenerationGraph degenerationGraph(V,E,C) == V#7);
rays7 = for C in cones7 list rays C
allRays = first rays7;
for i from 1 to #cones7-1 do allRays = allRays | rays7#i;
C7 = rays coneFromVData allRays

isHilbSegment V#8

isHilbSegment V#9
cones9 = select(conesMaxDim, C -> first maximalElementsDegenerationGraph degenerationGraph(V,E,C) == V#9);
rays9 = for C in cones9 list rays C
allRays = first rays9;
for i from 1 to #cones9-1 do allRays = allRays | rays9#i;
C9 = rays coneFromVData allRays

isHilbSegment V#10
cones10 = select(conesMaxDim, C -> first maximalElementsDegenerationGraph degenerationGraph(V,E,C) == V#10);
rays10 = for C in cones10 list rays C
allRays = first rays10;
for i from 1 to #cones10-1 do allRays = allRays | rays10#i;
C10 = rays coneFromVData allRays

isHilbSegment V#11
cones11 = select(conesMaxDim, C -> first maximalElementsDegenerationGraph degenerationGraph(V,E,C) == V#11);
rays11 = for C in cones11 list rays C
allRays = first rays11;
for i from 1 to #cones11-1 do allRays = allRays | rays11#i;
C11 = rays coneFromVData allRays

W = C0 | C1 | C2 | C3 | C5 | C6 | C7 | C9 | C10 | C11;
rays coneFromVData W

-- (2) Figure 10(A)
restart
loadPackage("StronglyStableIdeals");
loadPackage("Polyhedra",Reload=>true);
loadPackage("GroebnerFanHilbertScheme");
R = QQ[x_3,x_2,x_1,x_0];
J = ideal(x_3^2,x_2*x_3,x_2^3,x_1*x_2^2,x_1^2*x_3,x_1^2*x_2,x_1^3)
hp = hilbertPolynomial J
L = ideal(x_3,x_2,x_1^8)
J1 = findCloserVertex(J,L,MonomialOrder=>GLex)
J2 = findCloserVertex(J1,L,MonomialOrder=>GLex)
J3 = findCloserVertex(J2,L,MonomialOrder=>GLex)
J4 = findCloserVertex(J3,L,MonomialOrder=>GLex)
J5 = findCloserVertex(J4,L,MonomialOrder=>GLex)

netList findPathToRoot(J,L,MonomialOrder=>GLex)
borelGraphDistance(J,L)
netList findShortestPath(J,L)
    
borelGraphDistanceMatrix borelGraph(hp,R)
maxDistance = max flatten entries oo


--------------------------------------------------------------------------------
----  Example 4.16 - pag. 33-34                                             ----
--------------------------------------------------------------------------------
-- (1) Figure 10(B)
restart
loadPackage("StronglyStableIdeals");
loadPackage("Polyhedra",Reload=>true);
loadPackage("GroebnerFanHilbertScheme");
R = QQ[x_3,x_2,x_1,x_0];
hp = 6*projectiveHilbertPolynomial 1 - 9*projectiveHilbertPolynomial 0;
r = gotzmannNumber hp;
(V,E,F) = groebnerFan(hp,R);
#V, #E
extremalRays = rays F;
conesMaxDim = for mc in maxCones F list coneFromVData extremalRays_mc;
#conesMaxDim, numColumns extremalRays

for C in conesMaxDim do (
    print "\nNew cone:";	  
    print (rays C);
    maxElements = maximalElementsDegenerationGraph degenerationGraph(V,E,C);   
    if #maxElements == 1 then
    (
    	print "Unique maximal element (nothing to check)";
    )
    else
    (
	print "Maximal elements:";
	print netList maxElements; 
	W = sum entries transpose rays C;
	notComparable = true;
	for i from 0 to #maxElements-2 do
	(
	    Ifrak = flatten entries gens truncate(r,maxElements#i);
	    for j from i+1 to #maxElements-1 do
	    (		
		Jfrak = flatten entries gens truncate(r,maxElements#j);
		notComparable = notComparable and compareSetsOfMonomials(Ifrak,Jfrak,MonomialOrder=>{Weights=>W}) === null;  
	    );  
	);
    	if notComparable then print "Comparable pairs: none" else print "Comparable pairs: found";	
    );
);


--------------------------------------------------------------------------------
----  Example 4.16 - pag. 33-34                                             ----
--------------------------------------------------------------------------------
restart
loadPackage("StronglyStableIdeals");
loadPackage("Polyhedra",Reload=>true);
loadPackage("GroebnerFanHilbertScheme");
R = QQ[x_3,x_2,x_1,x_0];
hp = 6*projectiveHilbertPolynomial 1 - 9*projectiveHilbertPolynomial 0;
r = gotzmannNumber hp;
(V,E,F) = groebnerFan(hp,R);
irregularIdeals = select(V, J -> isIrregular(J,V,E));
#irregularIdeals
netList for J in irregularIdeals list {J,if (SC = segmentCone(J,r)) =!= null then rays SC,if (MC = maximalityCone(J,V,E)) =!= null then rays MC}

regularIdeals = select(V, J -> not isIrregular(J,V,E));
#regularIdeals
netList for J in regularIdeals list {J,if (SC = segmentCone(J,r)) =!= null then rays SC}

extremalRays = rays F;
conesMaxDim = for mc in maxCones F list coneFromVData extremalRays_mc;
hilbSegmentCones = select(for J in V list segmentCone(J,r), C -> C =!= null);
#hilbSegmentCones
surelyWithMaximum = {};
for C in conesMaxDim do (
    intersectsHilbSegmentCones = false;
    i = 0;
    while i < #hilbSegmentCones and not intersectsHilbSegmentCones do
    (
    	intersectsHilbSegmentCones = dim intersection(C,hilbSegmentCones#i) == 4;
    	i = i+1;	
    );
    if intersectsHilbSegmentCones then surelyWithMaximum = append(surelyWithMaximum,C);
)
#surelyWithMaximum

conesWith3maximalElements = select(conesMaxDim,C -> length maximalElementsDegenerationGraph degenerationGraph(V,E,C) == 3); 
#conesWith3maximalElements
netList (maxElements = for C in conesWith3maximalElements list maximalElementsDegenerationGraph degenerationGraph(V,E,C))
maxElements = flatten unique maxElements;

MC = intersection for J in maxElements list maximalityCone(J,V,E);
unionOfCones = coneFromVData( rays conesWith3maximalElements#0 | rays conesWith3maximalElements#1 | rays conesWith3maximalElements#2 | rays conesWith3maximalElements#3 );
rays MC, rays unionOfCones
MC == unionOfCones


--------------------------------------------------------------------------------
----  Example 4.24 - pag. 37                                                ----
--------------------------------------------------------------------------------
restart
loadPackage("StronglyStableIdeals");
loadPackage("Polyhedra",Reload=>true);
loadPackage("GroebnerFanHilbertScheme");
R = QQ[x_3,x_2,x_1,x_0];
hp = 6*projectiveHilbertPolynomial 1 - 9*projectiveHilbertPolynomial 0;
r = gotzmannNumber hp;
(V,E,F) = groebnerFan(hp,R);
time lowerBoundNumberIrreducibleComponents(V,E,F)
time lowerBoundNumberIrreducibleComponents(V,E,F,Conjecture=>true)

H = unique for J in V list trim sub(J,x_1=>1)
extremalRays = rays F;
conesMaxDim = for mc in maxCones F list coneFromVData extremalRays_mc;
conesWith3maximalElements = select(conesMaxDim,C -> length maximalElementsDegenerationGraph degenerationGraph(V,E,C) == 3); 
maxElements = flatten unique for C in conesWith3maximalElements list maximalElementsDegenerationGraph degenerationGraph(V,E,C)
for J in maxElements list trim sub(J,x_1=>1)


--------------------------------------------------------------------------------
----  Example 4.26 - pag. 37-38                                             ----
--------------------------------------------------------------------------------
restart
loadPackage("StronglyStableIdeals");
loadPackage("Polyhedra",Reload=>true);
loadPackage("GroebnerFanHilbertScheme");
R = QQ[x_3,x_2,x_1,x_0];
hp = 7*projectiveHilbertPolynomial 1 - 12*projectiveHilbertPolynomial 0;
r = gotzmannNumber hp;
(V,E) = borelGraph(hp,R);
H = unique for J in V list trim sub(J,x_1=>1)
SH1 = select(V, J-> trim sub(J,x_1=>1) == H#0);
SH2 = select(V, J-> trim sub(J,x_1=>1) == H#1);
SH3 = select(V, J-> trim sub(J,x_1=>1) == H#2);
SH4 = select(V, J-> trim sub(J,x_1=>1) == H#3);
#SH1, #SH2, #SH3, #SH4

MC = maximalityCone(SH4#0,V,E);
rays MC

candidateSH3 = select(SH3, J -> maximalityCone(J,V,E) =!= null and dim intersection(MC, maximalityCone(J,V,E)) == 4)
MC3 = maximalityCone(candidateSH3#0,V,E);
rays MC3, rays MC, rays (MC = intersection(MC, MC3))

candidateSH2 = select(SH2, J -> maximalityCone(J,V,E) =!= null and dim intersection(MC, maximalityCone(J,V,E)) == 4)
MC2 = maximalityCone(candidateSH2#0,V,E);
rays MC2, rays MC, rays (MC = intersection(MC, MC2))

candidateSH1 = select(SH1, J -> maximalityCone(J,V,E) =!= null and dim intersection(MC, maximalityCone(J,V,E)) == 4)
MC1' = maximalityCone(candidateSH1#0,V,E);
rays MC1', rays MC, rays (MC' = intersection(MC, MC1'))
MC1 = maximalityCone(candidateSH1#1,V,E);
rays MC1, rays MC, rays (MC = intersection(MC, MC1))

W' = sum entries transpose rays MC';
maxElements' = maximalElementsDegenerationGraph degenerationGraph(V,E,W') 

W = sum entries transpose rays MC;
maxElements = maximalElementsDegenerationGraph degenerationGraph(V,E,W) 

netList maxElements',netList maxElements