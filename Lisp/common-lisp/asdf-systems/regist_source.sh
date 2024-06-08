
currentDir=`pwd`


ls ~/.config/common-lisp/source-registry.conf.d/
mkdir -p ~/.config/common-lisp/source-registry.conf.d/
cd ~/.config/common-lisp/source-registry.conf.d/
touch adsf-systems.conf

echo '(:tree "'$currentDir'/")' > asdf-systems.conf

cd $currentDir
