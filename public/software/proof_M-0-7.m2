------------------------------------------------------------------------
----	PROOF OF FULTON'S CONJECTURE n = 7  --  PROPOSITIONS 3.1    ----
------------------------------------------------------------------------

-- Convex geometry formulation B
restart
loadPackage "M07";
n = 7;
N = dimAmbientSpace n, Nbar = dimPic n, M = dimSubspaceRelations n
I = setOfIndices n
Fnef = FnefCone n;
#Fnef
--netList Fnef
V = linearEquivalenceRelations n;
#V
VV = {V_0,V_1,V_2,V_3,V_4,V_5,V_6,V_7,V_8,V_11,V_12,V_14,V_16,V_18};
netList VV
numgens trim ideal VV == M

E0 = gens ring Fnef#0;
#E0, indexOfContainment(Fnef,E0,LP=>lpSolve)

elapsedTime (E1 = minkowskiSum(E0,for i from 0 to 0 list VV#i));
#E1, indexOfContainment(Fnef,E1,LP=>lpSolve)

elapsedTime (E2 = minkowskiSum(E0,for i from 0 to 1 list VV#i));
#E2, indexOfContainment(Fnef,E2,LP=>lpSolve)

elapsedTime (E3 = minkowskiSum(E0,for i from 0 to 2 list VV#i));
#E3, indexOfContainment(Fnef,E3,LP=>lpSolve)

elapsedTime (E4 = minkowskiSum(E0,for i from 0 to 3 list VV#i));
#E4, indexOfContainment(Fnef,E4,LP=>lpSolve)

elapsedTime (E5 = minkowskiSum(E0,for i from 0 to 4 list VV#i));
#E5, indexOfContainment(Fnef,E5,LP=>lpSolve)

elapsedTime (E6 = minkowskiSum(E0,for i from 0 to 5 list VV#i));
#E6, indexOfContainment(Fnef,E6,LP=>lpSolve)

elapsedTime (E7 = minkowskiSum(E0,for i from 0 to 6 list VV#i));
#E7, indexOfContainment(Fnef,E7,LP=>lpSolve)

--elapsedTime (E8 = minkowskiSum(E0,for i from 0 to 7 list VV#i));
--#E8, indexOfContainment(Fnef,E8,LP=>lpSolve)




-- Convex geometry formulation C
restart
loadPackage "M07";
n = 7;
N = dimAmbientSpace n, Nbar = dimPic n, M = dimSubspaceRelations n
(A1,A2) = quotientSpace (n,FontanariBasisPositions n);
R = A1#0; Rsub = A1#1; phiR = A1#2; inclR = A1#3;
W = A2#0; Wsub = A2#1; phiW = A2#2; inclW = A2#3;
B7 = gens Rsub
netList {R_0 => phiR(R_0), R_1 => phiR(R_1), R_2 => phiR(R_2),
         R_6 => phiR(R_6), R_8 => phiR(R_8), R_26 => phiR(R_26),
	 R_28 => phiR(R_28), R_40 => phiR(R_40), R_42 => phiR(R_42),
	 R_49 => phiR(R_49), R_50 => phiR(R_50), R_53 => phiR(R_53),
	 R_54 => phiR(R_54), R_55 => phiR(R_55)}
vectorToAdd = {phiR(R_1), phiR(R_50), phiR(R_8),  phiR(R_28),  phiR(R_42), 
               phiR(R_0), phiR(R_2), phiR(R_6), phiR(R_26), phiR(R_40),
	       phiR(R_49), phiR(R_53), phiR(R_54), phiR(R_55)};

Fnef = FnefCone(n,W);
FnefBar = for f in Fnef list phiW(f);

E0bar = gens Wsub;
#E0bar, indexOfContainment(FnefBar,E0bar,LP=>lpSolve)

elapsedTime E1bar = Vrepresentation2Hrepresentation(gens Rsub | for i from 0 to 0 list vectorToAdd#i,Wsub);
#E1bar, indexOfContainment(FnefBar,E1bar,LP=>lpSolve)

elapsedTime E2bar = Vrepresentation2Hrepresentation(gens Rsub | for i from 0 to 1 list vectorToAdd#i,Wsub);
#E2bar, indexOfContainment(FnefBar,E2bar,LP=>lpSolve)

elapsedTime E3bar = Vrepresentation2Hrepresentation(gens Rsub | for i from 0 to 2 list vectorToAdd#i,Wsub);
#E3bar, indexOfContainment(FnefBar,E3bar,LP=>lpSolve)

elapsedTime E4bar = Vrepresentation2Hrepresentation(gens Rsub | for i from 0 to 3 list vectorToAdd#i,Wsub);
#E4bar, indexOfContainment(FnefBar,E4bar,LP=>lpSolve)

elapsedTime E5bar = Vrepresentation2Hrepresentation(gens Rsub | for i from 0 to 4 list vectorToAdd#i,Wsub);
#E5bar, indexOfContainment(FnefBar,E5bar,LP=>lpSolve)

elapsedTime E6bar = Vrepresentation2Hrepresentation(gens Rsub | for i from 0 to 5 list vectorToAdd#i,Wsub);
#E6bar, indexOfContainment(FnefBar,E6bar,LP=>lpSolve)

elapsedTime E7bar = Vrepresentation2Hrepresentation(gens Rsub | for i from 0 to 6 list vectorToAdd#i,Wsub);
#E7bar, indexOfContainment(FnefBar,E7bar,LP=>lpSolve)
