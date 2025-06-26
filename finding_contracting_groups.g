# todo:
    # figure out good stopping point for nucleus depth
    # how many generators?
    # different probabilities?
    # keep track of success rate

new_autom_gr := function(T_d, numGenerators, oneProb)
    # T_d: d-ary tree, numGenerators: <= 40,

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

contracting_groups := function(T_d, numGenerators, numTries, nucleusDepth, oneProb)
    # T_d: d-ary tree, numGenerators: <= 20, nucleusDepth: where to quit, numTries: how many groups to generate
    # oneProb: Probability of a section being 1
    local aut_groups, G, nucleus, c_groups, counter;

    aut_groups := List([1..numTries], x -> new_autom_gr(T_d, numGenerators, oneProb));
    c_groups := [];

    counter := 0;
    for G in aut_groups do
        counter := counter + 1;
        Print("GROUP NUMBER ", counter, "\n");

        nucleus := FindNucleus(G, nucleusDepth, true);
        Print("\n\n\n");

        if nucleus <> fail then
            # contracting! yay!
            Append(c_groups, [G]);
            #Print("\n", G, " is contracting!\n");

        else
            #Print("\n", G, " is not contracting\n");
        fi;
    od;

    # check here if groups are isomorphic to known contracting automaton groups?

    return c_groups;
end;

countOnes := function(c_grs)
    # extend contracting groups to have more generators?
end;

RoundToDecimal := function(x, n)
    local factor;
    factor := 10^n;
    return Round(x * factor) / factor;
end;


testing_c_grs := function(p_list, num_gens_list, degree_list, num_tries_each, nucleus_max_size)
    local f, f2, d, g, p;

    # opening files
    f := OutputTextFile("c_gr_info.txt", true);
    f2 := OutputTextFile("c_grs.txt", true);

    for d in degree_list do
        # header :)
        AppendTo("c_gr_info.txt", "\n\n\n------\tCONTRACTING GROUPS: ", d, "-ARY TREE\t------\n");

        for g in num_gens_list do
            for p in p_list do
                # generating contracting groups
                cgs := contracting_groups(d, g, num_tries_each, nucleus_max_size, p);

                # printing them to console
                for i in [1..Length(cgs)] do
                    Print("\n\n", i, ". ", cgs[i]);
                od;
                Print("\n\n");

                # adding info to file
                AppendTo("c_gr_info.txt", "\n~ Num states: ");
                AppendTo("c_gr_info.txt", g);
                
                AppendTo("c_gr_info.txt", "\t~ Probability of 1: ");
                AppendTo("c_gr_info.txt", p);

                AppendTo("c_gr_info.txt", "\t~ Success rate: ");
                AppendTo("c_gr_info.txt", RoundToDecimal((1.0*Length(cgs))/(1.0*num_tries_each), 3));
                

                # keeping the contracting groups
                for i in [1..Length(cgs)] do
                    AppendTo("c_grs.txt", "\n\n\t~ Group: ");
                    AppendTo("c_grs.txt", cgs[i]);
                od;
                AppendTo("c_grs.txt", "\n\n");

                # simulating a flush
                CloseStream(f);
                CloseStream(f2);
                f := OutputTextFile("c_gr_info.txt", true);
                f2 := OutputTextFile("c_grs.txt", true);

            od;
        od;
    od;

    # close out files 
    CloseStream(f);
    CloseStream(f2);
end;

testing_c_grs([0.9, 0.8, 0.7, 0.6, 0.5, 0.4, 0.3, 0.2, 0.1], [5,4,3,2], [5,6,7,8], 30, 40);
