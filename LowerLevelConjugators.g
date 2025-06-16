LoadPackage("AutomGrp");
Reset(GlobalMersenneTwister,CurrentDateTimeString()); #new random seed
CONJUGATION_ACTION := OnPoints;
G := AutomatonGroup("a = (1, a, b, 1, c)(2, 5), b = (b, 1, b, b, 1)(1, 5)(2, 3, 4), c = (b, 1, 1, 1, b)(2, 3)(4, 5)");
N_LETTERS := DegreeOfTree(G);

g_list := List([1..10], i -> Random(StabilizerOfLevel(G, 4)));
r := Random(G);
h_list := List(g_list, x -> x^r);

findFirstNontrivialLevel := function(g)
    local i;
    i := 1;
    while PermOnLevel(g, i) = One(SymmetricGroup(N_LETTERS^i)) do 
        i := i + 1;
    od;
    return i;
end;

FindAllConjugators := function(G, g, h)
    local centralizer, r, coset;

    Print("Looking for centralizer...\n");
    centralizer := Centralizer(G, g); # centralizer of g
    Print("Looking for representative action...\n");
    r := RepresentativeAction(G, g, h, CONJUGATION_ACTION);
    Print("Computing coset...\n");
    coset := RightCoset(centralizer, r);
    Print("Coset found. There are ", Size(coset), " elements.\n");
    return coset;
end;

IntersectionOfConjugators := function(g_t, h_t, level)
    local sigma_g, sigma_h, ghConjugators, allConj, i;

    # getting tuples of g and h values
    Print("Calling FindAllConjugators, level ", level, " i = 1\n");
    ghConjugators := FindAllConjugators(PermGroupOnLevel(G, level), PermOnLevel(g_t[1], level), PermOnLevel(h_t[1], level));
    i := 2;
    while Size(ghConjugators) > 1 and i <= Length(g_t) do
        # all conjugators of a g/h pair
        sigma_g := PermOnLevel(g_t[i], level);
        sigma_h := PermOnLevel(h_t[i], level);
        Print("Calling FindAllConjugators, level ", level, "i = ", i, "\n");
        allConj := FindAllConjugators(PermGroupOnLevel(G, level), sigma_g, sigma_h);
        ghConjugators := Intersection(ghConjugators, allConj);
        i := i + 1;
    od;
    return ghConjugators;
end;

findConjugatorLowDown := function(gs, hs)
    local maxDepthToSearch, firstNontrivialLevels, firstNontrivialLevel, i,
        g, nontrivialGsOnLevel, nontrivialHsOnLevel, currentLevel, intersection;

    maxDepthToSearch := 1;
    Print("Finding non trivial levels\n");
    firstNontrivialLevels := NewDictionary(gs[1], true);
    for g in gs do 
        if g = One(G) then 
            continue;
        fi;
        firstNontrivialLevel := findFirstNontrivialLevel(g);
        maxDepthToSearch := Maximum(maxDepthToSearch, firstNontrivialLevel);
        AddDictionary(firstNontrivialLevels, g, firstNontrivialLevel);
    od;
    Print("maxDepthToSearch: ", maxDepthToSearch, "\n");

    nontrivialGsOnLevel := [];
    nontrivialHsOnLevel := [];
    for currentLevel in [1..maxDepthToSearch] do
        for i in [1..Length(gs)] do 
            if LookupDictionary(firstNontrivialLevels, gs[i]) = currentLevel then 
                Append(nontrivialGsOnLevel, [gs[i]]);
                Append(nontrivialHsOnLevel, [hs[i]]);
            fi;
        od;
        Print("Calling IntersectionOfConjugators on level ", currentLevel, "\n");
        if nontrivialGsOnLevel = [] then 
            continue;
        fi;
        intersection := IntersectionOfConjugators(nontrivialGsOnLevel, nontrivialHsOnLevel, currentLevel);
        if Size(intersection) = 1 then 
            return [currentLevel, Elements(intersection)[1]];
        fi;
    od;
    Print("Failure. There were ", Size(intersection), " elements in the intersection.\n");
    return fail;
end;

Print("Function call\n");
conj := findConjugatorLowDown(g_list, h_list);
Print("r was: ", r, "\n");
Print("current level: ", conj[1], " conjugator: ", conj[2], "\n");