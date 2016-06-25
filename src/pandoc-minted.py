# Copyright (c) 2015, Nick Ulle <nick.ulle@gmail.com>

# Permission to use, copy, modify, and/or distribute this software for any
# purpose with or without fee is hereby granted, provided that the above
# copyright notice and this permission notice appear in all copies.

# THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
# WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
# MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
# ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
# WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
# ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
# OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

# Source: https://github.com/nick-ulle/pandoc-minted

#!/usr/bin/env python
''' A pandoc filter that has the LaTeX writer use minted for typesetting code.

Usage:
    pandoc --filter ./minted.py -o myfile.tex myfile.md
'''

from string import Template
from pandocfilters import toJSONFilter, RawBlock, RawInline


def unpack_code(value, language):
    ''' Unpack the body and language of a pandoc code element.

    Args:
        value       contents of pandoc object
        language    default language
    '''
    [[_, classes, attributes], contents] = value

    if len(classes) > 0:
        language = classes[0]

    ###########################################
    # Added by Eric Bailey for Literate Idris #
    ###########################################
    if language == 'sourceCode':
        language = 'idris'
    ###########################################

    attributes = ', '.join('='.join(x) for x in attributes)

    return {'contents': contents, 'language': language,
            'attributes': attributes}


def unpack_metadata(meta):
    ''' Unpack the metadata to get pandoc-minted settings.

    Args:
        meta    document metadata
    '''
    settings = meta.get('pandoc-minted', {})
    if settings.get('t', '') == 'MetaMap':
        settings = settings['c']

        # Get language.
        language = settings.get('language', {})
        if language.get('t', '') == 'MetaInlines':
            language = language['c'][0]['c']
        else:
            language = None

        return {'language': language}

    else:
        # Return default settings.
        return {'language': 'text'}


def minted(key, value, format, meta):
    ''' Use minted for code in LaTeX.

    Args:
        key     type of pandoc object
        value   contents of pandoc object
        format  target output format
        meta    document metadata
    '''
    if format != 'latex':
        return

    # Determine what kind of code object this is.
    if key == 'CodeBlock':
        template = Template(
            '\\begin{minted}[$attributes]{$language}\n$contents\n\end{minted}'
        )
        Element = RawBlock
    elif key == 'Code':
        template = Template('\\mintinline[$attributes]{$language}{$contents}')
        Element = RawInline
    else:
        return

    settings = unpack_metadata(meta)

    code = unpack_code(value, settings['language'])

    return [Element(format, template.substitute(code))]


if __name__ == '__main__':
    toJSONFilter(minted)
