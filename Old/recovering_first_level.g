LoadPackage("AutomGrp");

N_LETTERS := 6; 
G := AutomatonGroup("a=(1,1,1,1,1,1)(1,4)(2,5)(3,6), b=(a,a,1,b,b,b), c=(a,1,a,c,c,c), d=(1,a,a,d,d,d)"); #universal grigorchuk group
CONJUGATION_ACTION := OnPoints; # action is conjugation

FindAllConjugators := function(G, g, h)
    local centralizer, r;

    centralizer := Centralizer(G, g); # centralizer of g
    r := RepresentativeAction(G, g, h, CONJUGATION_ACTION);
    return Elements(RightCoset(centralizer, r));
end;

IntersectionOfTuples := function(g_t, h_t)
    local ghConjugators, allConj, intersect, i;

    # getting tuples of g and h values
    ghConjugators := FindAllConjugators(PermGroupOnLevel(G, 1), g_t[1], h_t[1]);

    for i in [2..Length(g_t)] do
        # all conjugators of a g/h pair
        allConj := FindAllConjugators(PermGroupOnLevel(G, 1), g_t[i], h_t[i]);
        ghConjugators := Intersection(ghConjugators, allConj);
    od;
    return ghConjugators;
end;

#Modified from 2024 group
AreNotConjugateOnLevel:=function(a, b, max_level)
    local perm_group, level;
    for level in [1..max_level] do
         perm_group := PermGroupOnLevel(G, level);
        if not IsConjugate(PermGroupOnLevel(G, level), PermOnLevel(a, level), PermOnLevel(b, level)) then
            # Return true if NOT conjugate 
            return true; 
        fi;
    od;
    return false;
end;

TestConjugacyRelationships := function(g, h, candidate_sigma_r)
    local sigma_g, cycle_structure, orbits, sizesWithMultipleCycles, 
    fixed_points, size, orbits_of_size, valid_sigma_r, sigma_r, valid, 
    orbit, lhs, rhs, current_index, section;
    sigma_g := PermOnLevel(g, 1);
    cycle_structure := CycleStructurePerm(sigma_g);
    orbits := Orbits(Group(sigma_g));
    sizesWithMultipleCycles := []; 
    fixed_points := [1..N_LETTERS];
    if not IsOne(sigma_g) then
        SubtractSet(fixed_points, MovedPoints(sigma_g));
    fi;
    if Length(fixed_points) > 1 then 
        Append(sizesWithMultipleCycles, [1]);
    fi;
    for size in [1..Length(cycle_structure)] do
        if IsBound(cycle_structure[size]) and cycle_structure[size] > 1 then 
            #cycle_structure[1] is number of cycles of length 2
            Append(sizesWithMultipleCycles, [size + 1]);
        fi;
    od;
    valid_sigma_r := [];
    for sigma_r in candidate_sigma_r do
        valid := true;
        for size in sizesWithMultipleCycles do
            if size = 1 then 
                orbits_of_size := List(fixed_points, pt -> [pt]);
            else 
                orbits_of_size := Filtered(orbits, orbit -> Length(orbit) = size);
            fi;
            for orbit in orbits_of_size do
                #g_{a_1}g_{a_2}...g_{a_n} ~ h_{b_1}h_{b_2}...h_{b_n}
                lhs := One(G); #identity
                rhs := One(G);
                current_index := orbit[1];
                for section in [1..size] do 
                    lhs := lhs * Section(g, current_index);
                    rhs := rhs * Section(h, current_index^sigma_r);
                    current_index := current_index^sigma_g;
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
recoveringL1 := function(g_t, h_t)
    local possibleRs, sigma_gs, sigma_hs, i, sigma_g, fixed_points;
    sigma_gs := List(g_t, g -> PermOnLevel(g, 1));
    sigma_hs := List(h_t, h -> PermOnLevel(h, 1));

    #Get possible sigma_r by looking at permutations that could conjugate all sigma_g/sigma_h pairs
    possibleRs := IntersectionOfTuples(sigma_gs, sigma_hs);

    if Length(possibleRs) = 1 then
        return possibleRs[1];
    else
        #Narrow down possibilities for sigma_r by looking at conjugacy relationships between sections
        i := 1;
        while i <= Length(g_t) and Length(possibleRs) > 1 do
            sigma_g := sigma_gs[i];            
            fixed_points := [1..N_LETTERS];
                if not IsOne(sigma_g) then
                    SubtractSet(fixed_points, MovedPoints(sigma_g));
                fi;
            if fixed_points > 1 or Maximum(CycleStructurePerm(sigma_gs)) > 1 then 
                possibleRs := TestConjugacyRelationships(g_t[i], h_t[i], possibleRs);
            fi;
            i := i + 1;
        od;
        if Length(possibleRs) = 1 then 
            return possibleRs[1];
        else
            return fail;
        fi;

    fi;
end;