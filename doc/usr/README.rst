.. DO NOT EDIT, edit source/README.rst instead

Kind 2 User Documentation
=========================


Requirements
------------

In order to generate the documentation locally, you need:

* A GNU version of ``sed`` (``gsed`` on OSX)
* `Python v3.5 or later <https://www.python.org/downloads/>`_
* `Sphinx <https://www.sphinx-doc.org/en/master/usage/installation.html>`_

For HTML documentation, you additionally need:

* `sphinx-press-theme <https://pypi.org/project/sphinx-press-theme/>`_

For PDF documentation, you additionally need:

* `latexmk <https://personal.psu.edu/~jcc8/software/latexmk/>`_
* `XeTeX <https://xetex.sourceforge.net>`_
* `lmodern <https://www.gust.org.pl/projects/e-foundry/latin-modern>`_

If you're on Debian/Ubuntu, assuming you have Python 3 installed,
you can run the following:

.. code-block:: bash

    sudo apt-get install python3-sphinx latexmk texlive-xetex lmodern
    pip3 install sphinx_press_theme


Generating Documentation
------------------------

Run ``make`` or ``make all`` to generate both PDF and HTML documentation.
If only one format is desired, ``all`` can be substituted with either ``pdf`` or ``html``.

When documentation is generated, the ``README`` and ``LICENSE`` in the root of the
project are automatically replaced. If you want to modify those files, you should
edit the corresponding files in the ``source/`` directory.

When ``make`` is called, ``sed`` is invoked to convert
all internal references into explicit ones. This is needed in order for reST to
render on Github because the ``:ref:`` directive is not supported.

For files that need to be rendered on Github, ``include::`` directives must
be replaced with the contents of the included file. This is presently done for the
documentation README and the project root README, which both include ``source/doc_requirements.rst``.

Important Files
---------------

* ``source/home.rst``: The copy of the root README you should modify.
* ``source/README.rst``: The copy of this README you should modify.
* ``source/doc_requirements.rst``: Where requirements for generating documentation should be listed and edited.
* ``source/index.rst``: Where the documentation toctree is defined.
* ``source/conf.py``: All configuration settings, including LaTeX settings for PDF output.

Guidelines
------------

In order for the documentation to render properly, and for consistency,
please use the following headings (underline only):

..

    H1: =, H2: -, H3: ^, H4: ~, H5: ", H6: #

    =, for chapters
    -, for subsections
    ^, for subsubsections
    ~, for paragraphs

Prefer using the ``:ref:`` directive whenever possible to refer to other files,
as this directive renders properly in both PDF and HTML output. Only use external links
when it is needed, e.g. in the README that is on Github.

References
----------

* `reST and Sphinx cheat sheet <https://thomas-cokelaer.info/tutorials/sphinx/rest_syntax.html>`_
* `reST reference <http://docutils.sourceforge.net/rst.html>`_
* `Sphinx project configuration <https://www.sphinx-doc.org/en/master/usage/configuration.html>`_
* `Sphinx LaTeX customization <https://www.sphinx-doc.org/en/master/latex.html>`_
* `Sphinx directives reference <https://www.sphinx-doc.org/en/master/usage/restructuredtext/directives.html>`_

