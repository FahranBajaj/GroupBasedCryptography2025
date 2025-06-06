# the function take a protrait p and the degree of the tree as input to return the inverse of the portrait

PortraitInverse := function(p, degree)

    local inverse ;

    inverse := function(portrait)

        local k ;

        if not IsPerm(portrait[1]) then 

            return [portrait[1]^-1] ; 
        fi;

        if IsPerm(portrait[1]) then
            
            return Concatenation([portrait[1]^-1], List([1..degree], x-> inverse(portrait[x^(portrait[1]^-1)+1]) ) );
        fi;

    end;

    return inverse(p) ;
end;

# the function takes portrait , degree of the tree and the group as input and returns the pruned portrait.

PortraitPrune := function(portrait, degree , group)

    local nucleus, nucleus_identified , prune ;

    nucleus := List(GroupNucleus(group), x-> [x]) ; 

    nucleus_identified := List(nucleus , x -> [x,Concatenation([PermOnLevel(x[1],1)] , List([1..degree],y->[Sections(x[1])[y]]))  ]) ;

    # nucleus_identified := List(GroupNucleus(group) , x -> [[x],Concatenation([PermOnLevel(x,1)] , List([1..degree],y->[Sections(x)[y]]))  ]) ;

    prune := function(p) 

    local p_int , i ; 

        p_int := [] ;

        if p in nucleus then 
            return p ;

        else p_int := Concatenation([p[1]] , List([1..degree] , x-> prune(p[x+1]))) ;

            for i in [1..Length(nucleus_identified)] 
                do 
                    if p_int = nucleus_identified[i][2] then
                        return nucleus_identified[i][1];
                    fi;
                od;
            return p_int ;
        fi;
    end;

    return prune(portrait) ;
end;