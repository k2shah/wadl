import pytest
# os
import os
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
    path = os.path.join(os.path.dirname( __file__ ), '..', 'wadl', 'data', 'geofences')
    file = os.path.join(path, "croz_west")
    absfile = os.path.abspath(file)
    return Fence(absfile)

def test_fence(croz):
    # save figure to disk
    fig, ax = plt.subplots()
    croz.plot(ax)
    plt.savefig('tests/croz.png') 
    # sum of cords
    cordSum = [4.63967196e+08, 1.42278924e+09]
    assert all(abs(sum(croz.UTMCords)-cordSum)<1e4) , "file not parsed correctly"