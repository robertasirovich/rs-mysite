------------------------------------------------------------------
----	PROOF OF FULTON'S CONJECTURE n = 5  -- EXAMPLE 2.3    ----
------------------------------------------------------------------

-- Convex geometry formulation B
restart
loadPackage "M07";
n = 5;
N = dimAmbientSpace n, Nbar = dimPic n, M = dimSubspaceRelations n
I = setOfIndices n
Fnef = FnefCone n;
#Fnef
netList Fnef
V = linearEquivalenceRelations n;
#V
VV = {V_0,V_1,V_2,V_3,V_4};
netList VV
numgens trim ideal VV == M

E0 = gens ring Fnef#0;
#E0, indexOfContainment(Fnef,E0)

E1 = minkowskiSum(E0,VV#0);
netList E1
#E1, indexOfContainment(Fnef,E1)

E2 = minkowskiSum(E1,VV#1);
#E2, indexOfContainment(Fnef,E2)

E3 = minkowskiSum(E2,VV#2);
#E3, indexOfContainment(Fnef,E3)

E4 = minkowskiSum(E3,VV#3);
#E4, indexOfContainment(Fnef,E4)

E5 = minkowskiSum(E4,VV#4);
#E5, indexOfContainment(Fnef,E5)
netList E5


-- Convex geometry formulation C
restart
loadPackage "M07";
n = 5;
N = dimAmbientSpace n, Nbar = dimPic n, M = dimSubspaceRelations n
(A1,A2) = quotientSpace (n,FontanariBasisPositions n);
R = A1#0; Rsub = A1#1; phiR = A1#2; inclR = A1#3;
W = A2#0; Wsub = A2#1; phiW = A2#2; inclW = A2#3;
B5 = gens Rsub
netList {R_0 => phiR(R_0), R_1 => phiR(R_1), R_5 => phiR(R_5), R_8 => phiR(R_8), R_9 => phiR(R_9)}
vectorToAdd = {phiR(R_0), phiR(R_1), phiR(R_5), phiR(R_8), phiR(R_9)};

Fnef = FnefCone(n,W);
FnefBar = for f in Fnef list phiW(f);

E0bar = gens Wsub;
#E0bar, indexOfContainment(FnefBar,E0bar)
netList FnefBar, netList E0bar

E1bar = Vrepresentation2Hrepresentation(gens Rsub | for i from 0 to 0 list vectorToAdd#i,Wsub);
#E1bar, indexOfContainment(FnefBar,E1bar)

E2bar = Vrepresentation2Hrepresentation(gens Rsub | for i from 0 to 1 list vectorToAdd#i,Wsub);
#E2bar, indexOfContainment(FnefBar,E2bar)

E3bar = Vrepresentation2Hrepresentation(gens Rsub | for i from 0 to 2 list vectorToAdd#i,Wsub);
#E3bar, indexOfContainment(FnefBar,E3bar)

E4bar = Vrepresentation2Hrepresentation(gens Rsub | for i from 0 to 3 list vectorToAdd#i,Wsub);
#E4bar, indexOfContainment(FnefBar,E4bar)

E5bar = Vrepresentation2Hrepresentation(gens Rsub | for i from 0 to 4 list vectorToAdd#i,Wsub);
#E5bar, indexOfContainment(FnefBar,E5bar)
netList FnefBar, netList E5bar
