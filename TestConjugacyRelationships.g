LoadPackage("AutomGrp");
G := AutomatonGroup("a=(1,1)(1,2),b=(a,c),c=(a,d),d=(1,b)");
D := 2
SD := SymmetricGroup(D);

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
    size, orbitsOfSize, valid_sigma_r, sigma_r, valid, orbit, lhs, rhs, 
    current_index, section;

    sigma_g := PermOnLevel(g, 1);
    cycle_structure := CycleStructurePerm(sigma_g);
    orbits := Orbits(Group(sigma_g));
    sizesWithMultipleCycles := [];
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