import pytest
# os
import os
# plot
import matplotlib.pyplot as plt


@pytest.fixture
def croz():
    """test Fence class """
    # build fixture
    from wadl.lib.fence import Fence
    # cros test fixture
    path = os.path.join(os.path.dirname(__file__), 'data')
    file = os.path.join(path, "croz_west")
    absfile = os.path.abspath(file)
    return Fence(absfile)


def test_fence(croz):
    # save figure to disk
    fig, ax = plt.subplots()
    croz.plot(ax)
    rootDir = os.path.dirname(__file__)
    pathDir = os.path.join(rootDir, "out")
    if not os.path.exists(pathDir):  # make dir if not exists
        os.makedirs(pathDir)
    fileName = os.path.join(pathDir, 'croz.png')
    plt.savefig(fileName)
    # sum of cords
    cordSum = [4.63967196e+08, 1.42278924e+09]
    assert all(abs(sum(croz.UTMCords)-cordSum) <
               1e4), "file not parsed correctly"
