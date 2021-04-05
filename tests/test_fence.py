import pytest
# path
from pathlib import Path
# plot
import matplotlib.pyplot as plt


@pytest.fixture
def croz():
    """test Fence class """
    # build fixture
    from wadl.lib.fence import Fence
    # cros test fixture
    file = Path(__file__).parent / "data" / "croz_west"
    return Fence(file)


def test_fence(croz):
    # sum of cords
    cordSum = [4.63967196e+08, 1.42278924e+09]
    assert all(abs(sum(croz.UTMCords)-cordSum) <
               1e4), "file not parsed correctly"

    # save figure to disk
    fig, ax = plt.subplots()
    croz.plot(ax)
    pathDir = Path(__file__).parent / "out"
    pathDir.mkdir(exist_ok=True)  # make dir if not exists
    fileName = pathDir / 'croz.png'
    plt.gca().set_aspect('equal', adjustable='box')
    plt.savefig(fileName, bbox_inches='tight', dpi=200)


def test_areas():
    from wadl.lib.fence import Areas
    file = Path("data/HMR_tree_polygon_v2/doc.kml")
    areas = Areas(file)
    assert len(areas) == 7
