import pytest
# math
import numpy as np
import numpy.linalg as la
import numpy.random as rand
# plot
import matplotlib.pyplot as plt

@pytest.fixture
def croz():
    """test Fence class """
    # build fixture
    from wadl.lib.fence import Fence
    # cros test fixture
    return Fence("croz_west")

def test_fense(croz):
    # save figure to disk
    fig, ax = plt.subplots()
    croz.plot(ax)
    plt.savefig('tests/croz.png') 
    # sum of cords
    cordSum = [4.63967196e+08, 1.42278924e+09]
    assert all(abs(sum(croz.UTMCords)-cordSum)<1e4) , "file not parsed correctly"