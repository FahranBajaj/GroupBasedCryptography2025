# todo:
    # figure out good stopping point for nucleus depth
    # ways other than brute force to rule out random groups?
    # intermediate growth??????

new_autom_gr := function(T_d, numGenerators)
    # T_d: d-ary tree, numGenerators: <= 20,

    local possible_gens, sections, S_d, currentGen, i, j, myGens, currentAut;

    # ex: AutomatonGroup([ [ 1, 2, ()], [ 1, 2, (1,2) ] ], [ "a", "b" ]); (a=1, b=2, etc)
    # setup for a new automaton group
    possible_gens := ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t"];
    sections := [];
    S_d := SymmetricGroup(T_d);

    # making lists
    for i in [1..numGenerators] do  # make some generators!
        currentGen := [];

        for j in [1..T_d] do  # make some sections!
            Append(currentGen, [Random([1..numGenerators])]);       # QUESTION: how to get the identity in there?
        od;
        Print("Section: ", currentGen, "\n");

        Append(currentGen, [Random(Elements(S_d))]);  # appending random permutation!
        Append(sections, [currentGen]);
    od;

    # getting generators
    myGens := List([1..numGenerators], i -> possible_gens[i]);
    Print("Generators: ", myGens, "\n");

    # new automaton group!
    currentAut := AutomatonGroup(sections, myGens);
    Print("current aut gr: ", currentAut, "\n\n");
    
    return currentAut;
end;

# Print(new_autom_gr(6,4));

contracting_groups := function(T_d, numGenerators, numTries, nucleusDepth, moreOnes)
    # T_d: d-ary tree, numGenerators: <= 20, nucleusDepth: where to quit, numTries: how many groups to generate, moreOnes: t/f
    # Q: vary numGenerators? take a range? completely random?
    local aut_groups, G, nucleus, c_groups;

    aut_groups := List([1..numTries], x -> new_autom_gr(T_d, numGenerators));
    c_groups := [];


    for G in aut_groups do
        nucleus := FindNucleus(G, nucleusDepth);

        if nucleus <> fail then
            Print("\n\n\n!!!", G, " is contracting!!!\n\n\n");
            Append(c_groups, [G]);
        fi;
    od;

    # check here if groups are isomorphic to known contracting automaton groups?

    # write groups to file?

    return c_groups;
end;

cgs := contracting_groups(4,3,150,20,false);
Print("\n", cgs);