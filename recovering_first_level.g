LoadPackage("AutomGrp");
#Read( Filename( DirectoriesPackageLibrary( "automgrp", "tst" ), "testall.g"));

N_LETTERS := 4; # was 4
G := SymmetricGroup(N_LETTERS);
CONJUGATION_ACTION := OnPoints; # action is conjugation

FindAllConjugators := function(G, g, h)
    local centralizer, r;

    centralizer := Centralizer(G, g); # centralizer of g
    r := RepresentativeAction(G, g, h, CONJUGATION_ACTION); # 
    return RightCoset(centralizer, r);
end;

printMe := function()
    local conjugacyClasses, conjugacyClass, g, h;

    conjugacyClasses := ConjugacyClasses(G);
    for conjugacyClass in conjugacyClasses do
        for g in Elements(conjugacyClass) do 
            for h in Elements(conjugacyClass) do 
                Print("g: ", g, "\nh: ", h, "\nPossible conjugators: ", FindAllConjugators(G, g, h), "\n\n");
            od;
            Print("\n------------------------------------------------------------\n");
        od;
        Print("\n*************************************************************\n*************************************************************\n");
    od;
end;

Print("\n\n******************************************************************************************\n");
Print("\t\t\t\tTUPLES OF Gs & Hs");
Print("\n******************************************************************************************\n\n");

IntersectionOfTuples := function(g_t, h_t, s_what)
    # s_what: which symmetric group number you want

    local G, gTuple, hTuple, ghConjugators, allConj, intersect, i;

    G := SymmetricGroup(s_what);
    # getting tuples of g and h values
    gTuple := [];
    Append(gTuple, g_t);
    hTuple := [];
    Append(hTuple, h_t);
    ghConjugators := [];

    for i in [1..Length(g_t)] do
        # all conjugators of a g/h pair
        allConj := FindAllConjugators(G,gTuple[i],hTuple[i]);
        Append(ghConjugators, [Elements(allConj)]);
        Print("g: ", gTuple[i], " h: ", hTuple[i], " all reps: ", ghConjugators[i], "\n");
        Print("\n------------------------------------------------------------\n");
    od;

    # finding the intersection of the tuples
    intersect := ghConjugators[1];

    for i in [1..Length(ghConjugators)] do
        intersect := Intersection(intersect, ghConjugators[i]);
    od;

    Print("\nIntersection of conjugators: ", intersect);
    return intersect;
end;

#Modified from 2024 group
AreNotConjugateOnLevel:=function(a, b, level)
    if not IsConjugate(PermGroupOnLevel(G, level), PermOnLevel(a, level), PermOnLevel(b, level)) then
        # Return true if NOT conjugate 
        return true; 
    fi;
    return false;
end;

TestConjugacyRelationships := function(g, h, candidate_sigma_r)
    local sigma_g, cycle_structure, orbits, sizesWithMultipleCycles, 
    size, orbitsOfSize, valid_sigma_r, sigma_r, valid, orbit, lhs, rhs, 
    current_index, section;

    sigma_g := PermOnLevel(g, 1);
    cycle_structure := CycleStructurePerm(sigma_g);
    orbits := Orbits(Group(sigma_g));
    sizesWithMultipleCycles := [];
    for size in [1..Length(cycle_structure)] do
        if cycle_structure[size] > 1 then 
            #cycle_structure[1] is number of cycles of length 2
            Append(sizesWithMultipleCycles, [size + 1]);
        fi;
    od;
    valid_sigma_r := [];
    for sigma_r in candidate_sigma_r do
        valid := true;
        for size in sizesWithMultipleCycles do
            orbitsOfSize := Filtered(orbits, orbit -> Length(orbit) = size);
            for orbit in orbitsOfSize do
                #g_{a_1}g_{a_2}...g_{a_n} ~ h_{b_1}h_{b_2}...h_{b_n}
                lhs := (1); #identity
                rhs := (1);
                current_index := orbit[1];
                for section in [1..size - 1] do 
                    lhs := lhs * Section(g, current_index);
                    rhs := rhs * Section(g, current_index^sigma_r);
                od;
                if AreNotConjugateOnLevel(lhs, rhs, 4) then
                     valid := false;
                     break;
                fi;
            od;
            if not valid then 
                break;
            fi;
        od;
        if valid then
            Append(valid_sigma_r, [sigma_r]);
        fi;
    od;
    return valid_sigma_r;
end;


# THE ACTUAL PROCESS
recoveringL1 := function(sigma_g, sigma_h, s_what)
    local possibleRs;

    possibleRs := IntersectionOfTuples(sigma_g, sigma_h, s_what);

    if Length(possibleRs) = 1 then
        Print("\n\n\n**********************************************************************\n");
        Print("Sigma_r is equal to ", possibleRs[1]);
        Print("\n**********************************************************************\n\n\n");
    else
        Print("\n\nTrying to narrow down ", possibleRs, "...\n");
        # fahran's method goes here
        possibleRs := TestConjugacyRelationships(sigma_g, sigma_h, possibleRs);
        Print("\nPossible sigma_rs: ", possibleRs);
    fi;
end;

recoveringL1([(1,3,2),(1,2,3)], [(1,2,3),(1,3,2)],4);