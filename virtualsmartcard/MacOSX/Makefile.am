EXTRA_DIST = MacOSX_install/postinstall MacOSX_uninstall/postinstall

all-local:
	@echo Use \`$(MAKE) osx\` to compile package for Mac OS X



OSX_TOOLS_DIR = "$(shell xcode-select -p)/Platforms/MacOSX.platform/Developer/SDKs"
OSX_TOOL_DIR ?= "$(OSX_TOOLS_DIR)/$(shell ls -1 $(OSX_TOOLS_DIR) | sort -n -k2 -t. -r | head -1)/usr"
OSX_TARGETDIR = $(abs_top_builddir)/$(PACKAGE_TARNAME)-$(PACKAGE_VERSION)_osx
osx:
	rm -rf $(OSX_TARGETDIR) dmg $(top_builddir)/$(PACKAGE_TARNAME)-$(PACKAGE_VERSION)_osx.dmg
	@echo Configuring virtualsmartcard for IFD bundle
	cd $(top_builddir) && ./configure --enable-infoplist --prefix=/Library/VirtualSmartCard \
		CFLAGS="-arch x86_64 -arch arm64" \
		--enable-serialdropdir=/usr$(OSX_SERIAL_LOCAL_PREFIX)/libexec/SmartCardServices/drivers/ifd-vpcd.bundle/Contents/MacOS \
		--enable-serialconfdir=/usr$(OSX_SERIAL_LOCAL_PREFIX)/libexec/SmartCardServices/drivers/ifd-vpcd.bundle/Contents
	@echo Compiling virtualsmartcard
	make -C $(top_builddir) clean install DESTDIR=$(OSX_TARGETDIR)
	@echo Configuring virtualsmartcard for builtin libpcsclite
	cd $(top_builddir) && ./configure --enable-infoplist --prefix=/Library/VirtualSmartCard \
		CFLAGS="-arch x86_64 -arch arm64" \
		--enable-serialdropdir=/usr$(OSX_SERIAL_LOCAL_PREFIX)/libexec/SmartCardServices/drivers/ifd-vpcd.bundle/Contents/MacOS \
		--enable-serialconfdir=/usr$(OSX_SERIAL_LOCAL_PREFIX)/libexec/SmartCardServices/drivers/ifd-vpcd.bundle/Contents \
		--enable-libpcsclite
	@echo Compiling virtualsmartcard
	make -C $(top_builddir) clean install DESTDIR=$(OSX_TARGETDIR)
	mv $(OSX_TARGETDIR)/usr $(OSX_TARGETDIR)/Library/VirtualSmartCard/usr
	pkgbuild --root $(OSX_TARGETDIR) --scripts MacOSX_install --identifier com.vsmartcard.virtualsmartcard.mac --version $(PACKAGE_VERSION) --install-location / VirtualSmartCard-$(PACKAGE_VERSION)_install.pkg
	pkgbuild --nopayload --identifier com.vsmartcard.virtualsmartcard.mac.uninstall --scripts MacOSX_uninstall Uninstall_VirtualSmartCard.pkg
	mkdir -p dmg
	cp *.pkg dmg
	hdiutil create -srcfolder dmg -volname "$(PACKAGE_STRING) for Mac OS X" $(top_builddir)/$(PACKAGE_TARNAME)-$(PACKAGE_VERSION)_osx.dmg
