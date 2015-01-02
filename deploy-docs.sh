#!/bin/bash

set -e

rev=$(git rev-parse --short HEAD)

cd target/doc

git init
git config --global user.name "doc bot"
git config --global user.email "docbot@travis"
git remote add upstream "https://$GH_TOKEN@github.com/Gankro/collect-rs.git"
git fetch upstream
git reset upstream/gh-pages

touch .

git add -A .
git commit -m "rebuild pages at ${rev}"
git push upstream HEAD:gh-pages
