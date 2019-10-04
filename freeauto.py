import itertools
import unittest
import string
from hypothesis import given, reproduce_failure, strategies as st

###########################################################################
#
# Human-readable representation
#
# We'll use strings of alphabetical characters, with
# capital letters being the inverse of small letters
# A = a^{-1}, B = b^{-1}, etc.
###########################################################################
def parse_char( char ):
    if char.isupper():
        return -( ord( char ) - ord( 'A' ) + 1 )
    else:
        return ord( char ) - ord( 'a' ) + 1
    
def parse( word ):
    return [ parse_char( c ) for c in word ]

def unparse_char( e ):
    if e > 0:
        return chr( e - 1 + ord( 'a' ) )
    else:
        return chr( -e - 1 + ord( 'A' ) )
    
def unparse( word ):
    return "".join( unparse_char(e) for e in word )

###########################################################################
#
# Free group operations and automorphisms
#
# The group operation is just +.
#
###########################################################################

def basis( rank ):
    return range( 1, rank+1 )

def invert( word ):
    tmp = [ -a for a in word ]
    tmp.reverse()
    return tmp
        
def cyclic_reduce( word ):
    if len( word ) == 0:
        return word
    
    reduced = []
    for a in word:
        if len( reduced ) > 0 and -a == reduced[-1]:
            reduced.pop()
        else:
            reduced.append( a )

    while len( reduced ) >= 2:
        if -reduced[0] == reduced[-1]:
            reduced = reduced[1:-1]
        else:
            break
        
    return reduced

def flatten_1( list_of_words ):
    ret = []
    for word in list_of_words:
        ret.extend( word )
    return ret
    
def automorphism_from_basis( basis_map, **kwargs ):
    def use_basis( a ):
        if a > 0:
            return basis_map[a]
        else:
            return invert( basis_map[-a] )
        
    def f( word ):
        # If we flatten ahead of time then f(x) + f(y) != f(x+y)
        return flatten_1( use_basis(a) for a in word )

    f.map = basis_map
    for k, v in kwargs.items():
        setattr(f, k, v)
    return f

def conjugacy_class_rep( w ):
    """Find the lexicographically minimal of the conjugacy class, which
    consists of all cyclic permutations of the word."""
    w = cyclic_reduce( w )
    if len( w ) == 0:
        return []
    return min( w[r:] + w[:r] for r in range( len( w ) ) )

###########################################################################
#
# Whitehead automorphisms
#
###########################################################################

def all_inversions( permutation ):
    for ops in itertools.product( [lambda x : [x], lambda x : [-x]],
                                  repeat=len( permutation ) ):
        yield [ f(x) for f, x in zip( ops, permutation ) ]
    
def whitehead_automorphisms( rank ):
    bs = basis( rank )
    
    # The identity is listed both places... filter it?
    # Type 1
    for p in itertools.permutations( bs ):
        for pi in all_inversions( p ):
            basis_map = dict( zip( bs, pi ) )
            yield automorphism_from_basis( basis_map, kind=1 )

    # Type 2
    for e in bs:
        for a in [ e, -e ]:
            # all non-a elements x are mapped to one of
            # x, xa, a^{-1}x, a^{-1}xa
            choices = [ lambda x : [x],
                        lambda x : [x, a],
                        lambda x : [-a, x],
                        lambda x : [-a, x, a] ]
            not_a = [x for x in bs if x != a and x != -a ]
            a_self = [ (e, [e]) ]
            for choice in itertools.product( choices, repeat=len( not_a ) ):
                partial_aut = [ (x,f(x)) for f,x in zip( choice, not_a ) ]
                basis_map =  dict( a_self + partial_aut )
                yield automorphism_from_basis( basis_map, kind=2, multiplier=a )

###########################################################################
#
# Whitehead graph
#
# Nodes are conjugacy classes.
# Edges are length-preserving Whitehead automorphisms.
#
###########################################################################

import itertools

def conjugacy_classes( rank, length ):
    elements = list( basis(rank) ) + invert( basis( rank ) )
    classes = set()
    for word in itertools.product( elements, repeat=length ):
        c = conjugacy_class_rep( word )
        if len( c ) == length:
            classes.add( tuple( c ) )
            
    return classes

def show_classes( rank, length ):
    line = ""
    for c in conjugacy_classes( rank, length ):
        line += "[" + unparse( c ) + "] "
        if len( line ) + length + 3 > 80:
            print( line )
            line = ""

    if line != "":
        print( line )

class Component(object):
    def __init__( self, name ):
        self.name = name
        self.size = 0
        self.diameter = 0

    def __str__( self ):
         return "Component " +  self.name + \
                   " size " + str(self.size) + \
                   " diameter <= " + str(self.diameter)
    
def summarize_graph( rank, length ):
    print( "Rank", rank, "length", length )
    classes = conjugacy_classes( rank, length )
    print( len( classes ), "conjugacy classes" )
    visited = set()
    components = []

    automorphisms = list( whitehead_automorphisms( rank ) )
    print( len( automorphisms ), "automorphisms" )
    
    while len( classes ) > 0:
        next_component = classes.pop()
        queue = set( [next_component] )
        name = "[" + unparse( next_component ) + "]"
        depth = { next_component : 0 }

        cc = Component( name )
        while len( queue ) > 0:
            current = queue.pop()
            visited.add( current )
            cc.size += 1
            for f in automorphisms:
                v = tuple( conjugacy_class_rep( f( current ) ) )
                if len( v ) != length:
                    continue
                if v in visited or v in queue:
                    continue
                classes.remove( v )
                queue.add( v )
                depth[v] = depth[current] + 1
                #print( unparse( current ), "->", unparse( v ), depth[v] )

        cc.diameter = max( depth.values() ) * 2
        print( cc )
        components.append( cc )
        
    return components

import pprint

def show_rank( rank, minLength = 2 ):
    results = []
    try:
        for l in itertools.count( minLength ):
            cc = summarize_graph( rank, l )
            maxCC = max( cc, key = lambda x : x.size )
            results.append( ( l, maxCC.size, maxCC.name ) )
            pprint.pprint( results )
    except KeyboardInterrupt:
        pprint.pprint( results )
    return results
    
        
###########################################################################
# 
# Unit tests
#
###########################################################################

class ParseTests(unittest.TestCase):
    @given(st.text(alphabet=string.ascii_lowercase + string.ascii_uppercase))
    def test_identity(self, x):
            self.assertEqual( x, unparse(parse(x)) )

@st.composite
def word_of_rank( draw, rank ):
    elements = st.integers( -rank, rank ).filter( lambda x : x != 0 )
    return draw( st.lists( elements ) )

def element_of_rank( rank ):
    return st.integers( -rank, rank ).filter( lambda x : x != 0 )

class ReduceTests(unittest.TestCase):
    @given(st.lists(st.integers()))
    def test_reduce_idempotent(self, x):
        y = cyclic_reduce( x )
        z = cyclic_reduce( y )
        self.assertEqual( y, z )
        
    @given(word_of_rank(5),element_of_rank(5))
    def test_conjugacy_class(self,w,x):
        w2 = [-x] + w + [x]
        self.assertEqual( conjugacy_class_rep( w ),
                          conjugacy_class_rep( w2 ) )

class AutomorphismTests(unittest.TestCase):
    @given( word_of_rank( 4 ), word_of_rank( 4 ) )
    def test_automorphism(self, x, y ):
        for f in whitehead_automorphisms( 4 ):
            self.assertEqual( f( [] ), [] )
            self.assertEqual( f( invert( x ) ),
                              invert( f( x ) ) )
            self.assertEqual( f( x + y ),
                              f( x ) + f( y ),
                              "Function: " + str(f.map) )
        
def testAll():
    unittest.main(exit=False)
    

        
            
    
    
