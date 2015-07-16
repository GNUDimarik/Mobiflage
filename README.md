NOTICE:

PDE ( Plausible Deniable Encryption) for android. Created by Adam Skillen &amp; Mohammad Mannan

Original paper: http://spectrum.library.concordia.ca/975074

Website: http://users.encs.concordia.ca/~a_skil/mobiflage/

License: https://github.com/x942/mobiflage/blob/master/NOTICE


Mobiflage
Android source code patches
-=-=-=-=-=-=-=-=-=-=-=-=-=-


1. Place the mobiflage patch file AOSP source root directory.  
   Execute the patch using:
      
      $ patch -p0 < mf-mtp.patch
 
2. Place the kernel patch file for your kernel version in the 
   [KERNEL-SRC]/fs/ext4 directory.  Execute the patch using:
      
      $ patch < ialloc_3.x.patch
	
	Where x is kernel version you are using.

3. Make sure you compile the kernel with XTS and gfmul128 crypto support, 
   and place it in the [ANDROID-SRC]/device/[VENDOR]/[PRODUCT]/ directory.
   The file must be named "kernel".  For example, the Nexus S kernel binary 
   should be placed at [ANDROID-SRC]/device/samsung/crespo/kernel
 
4. The included ARM binaries for the mke2fs and tune2fs tools from the e2fsprogs package
   should be included in the /system/bin folder on the device.
 
 For additional information, and contirbutor contact information please see the 
 project website:
 http://users.encs.concordia.ca/~a_skil/mobiflage/

New features:
Ported to android kitkat
Add new feature with third password. When used enter third password hidden volume wipes and system starts with empty hidden volume
