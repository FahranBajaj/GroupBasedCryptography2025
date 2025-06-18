LoadPackage("AutomGrp");

#Returns a random element of the subgroup over which the Grigorchuk group is branching
RandomSubgroupElementGrigorchuk := function()
    local G, g, num_repetitions;
    G := AutomatonGroup("a = (1, 1)(1, 2), b = (a, c), c = (a, d), d = (1, b)");
    g := Random(G);
    num_repetitions := Random([-10..10]);
    return g^-1 * (a*b)^(2*num_repetitions) * g;
end;

#Returns an element that stabilizes the nth level, given a method that generates
#random elements of the subgroup over which G is branching
RandomStabilizerNthLevel := function(level, RandomSubgroupElement, degree)
    if level = 0 then 
        return RandomSubgroupElement();
    fi;

    return TreeAutomorphism(List([1..degree], i -> RandomStabilizerNthLevel(level - 1, RandomSubgroupElement, degree)), ());
end;
