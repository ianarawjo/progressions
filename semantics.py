from multiset import FrozenMultiset as Multiset
from set_util import powerset

def without_omega(l):
    return (l.count('xxx') == 0) or (l.count('xxx') == 1 and l.count('xx') == 0)

def irreducable(a):
    return any(x in a for x in ['_', '==', 'x'])

def simplify(s):
    return s.split('(')[0] + (('->' + s.split('->')[1]) if '->' in s else '')

def concept(name, expr=None, reduction=None):
    args = "()"
    if expr != None:
        if isinstance(expr, str): expr = [expr] # otherwise .join will treat strings as an array of chars
        args = "(" + ",".join(expr) + ")"
    return name.upper() + args + (('->' + reduction) if reduction != None else '')

# Takes some expression x
# and the _rest_ of the expressions on the board, M.
def try_reduce(x, M):

    if '_' in x:
        # Replace (if possible) first _ in x with something in M...
        # TODO: Remove duplicates.

        # SPECIAL exclusion criteria: Don't let _ in == be replaced by 'true' or 'false'!
        return [((M - Multiset([n])) + Multiset([x.replace('_', n, 1)]), concept('fill', str(n))) for n in M if
                (not 'x' in n and not '==' in n and not 'true' in n and not 'false' in n)]
    elif '==' in x:
        # Reduce completed equality expression:
        # (parse out left and right side and reduce to true or false...)
        idx = x.find('==')
        p, q = x[:idx].strip(), x[(idx+2):].strip()
        if p == q:
            return [ (M + Multiset(['true']), concept('eq', (p, q), 'true')) ]
        else:
            return [ (M + Multiset(['false']), concept('eq', (p, q), 'false')) ]
    elif x == 'xxx':
        return [(M + Multiset([n]) + Multiset([n]), concept('triple', str(n))) for n in M if not (not('_' in x) and '==' in x)]
    elif x == 'xx':
        return [(M + Multiset([n]), concept('double', str(n))) for n in M if not (not('_' in x) and '==' in x)]
    elif x == 'x' and len(M) > 0:
        return [(M, concept('iden'))]
    else:
        return []
