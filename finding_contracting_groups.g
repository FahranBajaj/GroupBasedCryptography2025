# todo:
    # figure out good stopping point for nucleus depth
    # ways other than brute force to rule out random groups?
LoadPackage("AutomGrp");
Reset(GlobalMersenneTwister,CurrentDateTimeString()); #new random seed
new_autom_gr := function(T_d, numGenerators, oneProb)
    # T_d: d-ary tree, numGenerators: <= 20,

    local possible_gens, sections, S_d, identity, weightedSections, num1s, numOtherGen, currentGen, i, j, myGens, currentAut;

    # ex: AutomatonGroup([ [ 1, 2, ()], [ 1, 2, (1,2) ] ], [ "a", "b" ]); (a=1, b=2, etc)
    # setup for a new automaton group
    possible_gens := ["1", "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t"]; # deal with 1!

    S_d := SymmetricGroup(T_d);

    sections := [];
    identity := [];
    Append(identity, List([1..T_d], x -> 1));
    Append(identity, [One(S_d)]);
    Append(sections, [identity]);

    # getting correct probability of 1s
    weightedSections := [];
    num1s := Int(oneProb*1000.0);
    numOtherGen := Int((1-oneProb)*1000.0/(numGenerators*1.0));

    Append(weightedSections, List([1..num1s], x -> 1));
    for i in [2..(numGenerators + 1)] do
        Append(weightedSections, List([1..numOtherGen], x -> i));
    od;

    # making lists
    for i in [2..(numGenerators+1)] do  # make some generators! skipping identity
        currentGen := [];

        for j in [1..T_d] do  # make some sections!
            # OLD: Append(currentGen, [Random([1..(numGenerators+1)])]);   # CHANGE THIS TO USE PROBABILITY!
            Append(currentGen, [Random(weightedSections)]);
        od;

        Append(currentGen, [Random(Elements(S_d))]);  # appending random permutation!
        Append(sections, [currentGen]);
    od;

    # getting generators
    myGens := List([1..(numGenerators+1)], i -> possible_gens[i]);

    # new automaton group!
    currentAut := AutomatonGroup(sections, myGens);
    
    return currentAut;
end;

# Print(new_autom_gr(6,4));

contracting_groups := function(T_d, numGenerators, numTries, maxNucleusSize, oneProb)
    # T_d: d-ary tree, numGenerators: <= 20, maxNucleusSize: where to quit, numTries: how many groups to generate
    # oneProb: Probability of a section being 1
    local aut_groups, G, nucleus, c_groups;

    aut_groups := List([1..numTries], x -> new_autom_gr(T_d, numGenerators, oneProb));
    c_groups := [];

    for G in aut_groups do
        nucleus := FindNucleus(G, maxNucleusSize, false);
        Print("*");

        if nucleus <> fail then
            # contracting! yay!
            Append(c_groups, [G]);
            #Print("\n", G, " is contracting!\n");

        else
            #Print("\n", G, " is not contracting\n");
        fi;
    od;

    # check here if groups are isomorphic to known contracting automaton groups?

    # write groups to file?

    return c_groups;
end;

cgs := contracting_groups(3,5,20,30,0.75);
Print("\n\nCONTRACTING GROUPS:");

for i in [1..Length(cgs)] do
    Print("\n\n", i, ". ", cgs[i], "\n");
    Print("Nucleus size: ", Size(GroupNucleus(cgs[i])), "\n");
od;
quit;