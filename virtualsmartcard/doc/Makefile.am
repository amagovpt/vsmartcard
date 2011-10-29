SUBDIRS = api

do_subst = sed \
	   -e 's,[@]PACKAGE_NAME[@],$(PACKAGE_NAME),g' \
	   -e 's,[@]PACKAGE_VERSION[@],$(PACKAGE_VERSION),g' \
	   -e 's,[@]builddir[@],$(builddir),g' \
	   -e 's,[@]prefix[@],$(prefix),g' \
	   -e 's,[@]exec_prefix[@],$(exec_prefix),g' \
	   -e 's,[@]libdir[@],$(libdir),g' \
	   -e 's,[@]includedir[@],$(includedir),g' \
	   -e 's,[@]VERSION[@],$(VERSION),g' \
	   -e 's,[@]OPENSC_LIBS[@],$(OPENSC_LIBS),g' \
	   -e 's,[@]top_srcdir[@],$(top_srcdir),g'

EXTRA_DIST = README.rst autotools.rst.in questions.rst.in

dist_noinst_SCRIPTS = generate_modules.py

.PHONY: doc
doc:
	$(do_subst) < autotools.rst.in > autotools.rst
	$(do_subst) < questions.rst.in > questions.rst
	./generate_modules.py $(top_srcdir)/src/vpicc --dest-dir=api --suffix=rst --no-toc -1

clean-local:
	rm -rf api/* autotools.rst questions.rst