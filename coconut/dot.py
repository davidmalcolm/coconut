#   Copyright 2014 David Malcolm <dmalcolm@redhat.com>
#   Copyright 2014 Red Hat, Inc.
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

# Helper functions for creating dot files:
def to_html(self):
    html_escape_table = {
        "&": "&amp;",
        '"': "&quot;",
        "'": "&apos;",
        ">": "&gt;",
        "<": "&lt;",

        # 'dot' doesn't seem to like these:
        '{': '\\{',
        '}': '\\}',
        }
    return "".join(html_escape_table.get(c,c) for c in str(self))

def _dot_column(text, align="left", colspan=1):
    return ('<td align="%s" colspan="%i">%s</td>'
            % (align, colspan, to_html(text)))

def dot_to_png(dot, filename):
    from subprocess import Popen, PIPE
    p = Popen(['/usr/bin/dot',
               '-T', 'png',
               '-o', filename],
              stdin=PIPE)
    p.communicate(dot.encode('utf-8'))
    p.wait()

def dot_to_svg(dot, filename):
    from subprocess import Popen, PIPE
    p = Popen(['/usr/bin/dot',
               '-T', 'svg',
               '-o', filename],
              stdin=PIPE)
    p.communicate(dot.encode('utf-8'))
    p.wait()
