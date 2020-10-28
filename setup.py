#!usr/bin/env python

"""The setup script."""

from setuptools import setup, find_packages

requirements = ['numpy', 'matplotlib', 'scipy', 'tqdm',
                'shapely', 'z3-solver', 'networkx', 'utm']

setup_requirements = ['pytest-runner', ]

test_requirements = ['pytest>=3', ]

setup(
    name="wadl-planner",
    author="Kunal Shah",
    author_email='k2shah@stanford.edu',
    python_requires='>=3.8',
    classifiers=[
        'Development Status :: 5 - Production/Stable',
        'Intended Audience :: Developers',
        'Natural Language :: English',
        'Programming Language :: Python :: 3.8',
    ],
    description="route planner for UAV surveys",
    install_requires=requirements,
    license="GNU General Public License v3 (GPL v3)",
    include_package_data=True,
    keywords='wadl',
    packages=find_packages(include=['wadl', 'wadl.*']),
    setup_requires=setup_requirements,
    test_suite='tests',
    tests_require=test_requirements,
    url='https://github.com/k2shah/wadl',
    version='1.0.1',
    zip_safe=False,
)
