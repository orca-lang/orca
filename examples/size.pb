data foo : set where
| baz : foo

data bar (a : set) : set_1 where
| foobar : foo -> bar a

def fooz : bar foo = foobar baz