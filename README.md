
# How to work with `gh-pages-src` branch
The `gh-pages-src` branch contains a config and `.md` files. All the
documentation can be done by modifying or adding `.md` files. They are located 
at `content` directory. 

The `gh-pages` branch contains auto-generated weg-pages using `Hugo` by compiling
`.md` files, theme and `config.toml` in gh-pages-src. The theme directory
contains code for a theme. The code is added as submodule.
You can 
1. compile -> run local server to test -> commit and push on `gh-pages-src` branch
2. compile -> deploy on gh-pages -> commit and push on `gh-pages-src` & `gh-pages`
   branches
3. commit and push on `gh-pages-src` -> contact me (I will do compilation and push)


## Download the code
```bash
git clone --recursive https://github.com/cornell-netlab/MicroP4.git
cd MicroP4
git checkout gh-pages-src # ignore warnings for couple of directories

# If you intend to compile after modifying .md files 
git submodule update --remote 
# If you intend to modify theme code
git submodule  update -f --checkout themes/ace-documentation
```
 

## Compile
The website is built using Hugo. Get Hugo.

### Install HUGO
Install `hugo_extended_0.72.0_*` from https://github.com/gohugoio/hugo/releases/tag/v0.72.0


### How to run local server
``` 
hugo server -w
```

### How to connect
```
http://localhost:1313/
```

### Prepare for public server, little tricky
```
// This will get gh-pages branch under public dir of this branch (gh-pages-src)
git worktree add -B gh-pages public origin/gh-pages
hugo // this will dump the compiled web-pages to `public` dir
```

### Commit and Push gh-pages
```
git commit -a -m "web-src-change" 
git push origin gh-pages
```

### Commit and Push .md modification
```
git commit -a -m "web-src-change" 
git push origin gh-pages-src
```

### Modifying Theme
The code for theme is added as submodule under themes dir of `gh-pages-src`.
ace-documentation theme is being used. You have read/write access to the repo..
