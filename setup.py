#!/usr/bin/env python3
#   Copyright 2013 David Malcolm <dmalcolm@redhat.com>
#   Copyright 2013 Red Hat, Inc.
#
#   This is free software: you can redistribute it and/or modify it
#   under the terms of the GNU General Public License as published by
#   the Free Software Foundation, either version 3 of the License, or
#   (at your option) any later version.
#
#   This program is distributed in the hope that it will be useful, but
#   WITHOUT ANY WARRANTY; without even the implied warranty of
#   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
#   General Public License for more details.
#
#   You should have received a copy of the GNU General Public License
#   along with this program.  If not, see
#   <http://www.gnu.org/licenses/>.

from setuptools import setup

setup(name='coconut',
    version='0.1',
    description='Experimental JIT compilation of Python 3 bytecode',
    packages=['coconut'],
    license='GPLv3 or later',
    author='David Malcolm <dmalcolm@redhat.com>',
    url='https://github.com/davidmalcolm/coconut/',
    classifiers=(
        'Intended Audience :: Developers',
        'Programming Language :: Python',
        'Programming Language :: Python :: 3',
        'Topic :: Software Development :: Libraries',
    ),
    test_suite='tests',
    test_loader='tests:TestLoader',
)
