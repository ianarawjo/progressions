from multiset import FrozenMultiset as Multiset
import random

# Generates the powerset of an iterable collection.
# Wrap this in list() to get the powerset as a sequence.
# Thanks to https://stackoverflow.com/a/1482320.
def powerset(s):
    if not isinstance(s, list): s = list(s) # convert to list if not a list...
    x = len(s)
    masks = [1 << i for i in range(x)]
    for i in range(1 << x):
        yield [ss for mask, ss in zip(masks, s) if i & mask]

# Chooses a random multiset subset of a set,
# i.e. allowing duplicates when randomly choosing from the set.
# It's like picking one thing out of a hat and putting it
# back in before picking another thing.
def random_multi_subset(s, num_elements):
    return Multiset([random.choice(list(s)) for _ in xrange(num_elements)])

def cumulative_combine_sets(list_of_sets):
    rst = []
    prev = Multiset()
    for s in list_of_sets:
        new_s = s + prev # set union
        rst.append( new_s )
        prev = new_s
    return rst
