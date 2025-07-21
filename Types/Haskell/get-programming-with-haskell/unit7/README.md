# Unit 7 Practical Haskell

## Lesson 39 Making Http Requests In Haskell, Lesson 40 Working With Json Data By Using Aeson

- http-json-example

> Windows.

```shell
$ stack update
$ stack new http-json-example
Downloading template new-template to create project http-json-example in directory http-json-example\...
Downloaded C:\Users\zhouj\AppData\Roaming\stack\templates\new-template.hsfiles.

Note: The following parameters were needed by the template but not provided: author-email, author-name, category, copyright and github-username.

      You can provide them in Stack's global YAML configuration file (C:\Users\zhouj\AppData\Roaming\stack\config.yaml) like this:

      templates:
        params:
          author-email: value
          author-name: value
          category: value
          copyright: value
          github-username: value

      Or you can pass each one on the command line as parameters like this:

      stack new http-json-example new-template -p "author-email:value" -p "author-name:value" -p "category:value" -p "copyright:value" -p "github-username:value"

Looking for Cabal or package.yaml files to use to initialise Stack's project-level YAML configuration file.

Using the Cabal packages:
* http-json-example\

Selecting the best among 21 snapshots...


Note: Matches https://raw.githubusercontent.com/commercialhaskell/stackage-snapshots/master/lts/22/11.yaml

Selected the snapshot https://raw.githubusercontent.com/commercialhaskell/stackage-snapshots/master/lts/22/11.yaml.
Initialising Stack's project-level YAML configuration file using snapshot https://raw.githubusercontent.com/commercialhaskell/stackage-snapshots/master/lts/22/11.yaml.
Considered 1 user package.
Writing configuration to http-json-example\stack.yaml.
Stack's project-level YAML configuration file has been initialised.


$ cd http-json-example
```

Update `resolver` in `stack.yaml` to use GHC-9.4.8 for debugging with [phoityne/ghci-dap](https://github.com/phoityne/ghci-dap).

```yaml
# DEV_ENV: 9.4.8
resolver: lts-21.25
```

Request NOAA token: https://www.ncdc.noaa.gov/cdo-web/token

```shell
$ stack setup

$ stack build

$ stack exec http-json-example-exe

$ stack repl
ghci> main   
"|gov.noaa.ncdc:C00861|1750-02-01|2024-03-12|Daily Summaries|1.0|GHCND|"
"|gov.noaa.ncdc:C00946|1750-02-01|2024-02-01|Global Summary of the Month|1.0|GSOM|"
"|gov.noaa.ncdc:C00947|1763-01-01|2024-01-01|Global Summary of the Year|1.0|GSOY|"
"|gov.noaa.ncdc:C00345|1991-06-05|2024-03-13|Weather Radar (Level II)|0.95|NEXRAD2|"
"|gov.noaa.ncdc:C00708|1994-05-20|2024-03-11|Weather Radar (Level III)|0.95|NEXRAD3|"
"|gov.noaa.ncdc:C00821|2010-01-01|2010-01-01|Normals Annual/Seasonal|1.0|NORMAL_ANN|"
"|gov.noaa.ncdc:C00823|2010-01-01|2010-12-31|Normals Daily|1.0|NORMAL_DLY|"
"|gov.noaa.ncdc:C00824|2010-01-01|2010-12-31|Normals Hourly|1.0|NORMAL_HLY|"
"|gov.noaa.ncdc:C00822|2010-01-01|2010-12-01|Normals Monthly|1.0|NORMAL_MLY|"
"|gov.noaa.ncdc:C00505|1970-05-12|2014-01-01|Precipitation 15 Minute|0.25|PRECIP_15|"
"|gov.noaa.ncdc:C00313|1900-01-01|2014-01-01|Precipitation Hourly|1.0|PRECIP_HLY|"
```

## Lesson 41 Using databases in Haskell

- sqlite-example

Set SQLite database file `databaseName` in `src/Lib.hs`.

```shell
$ stack repl
ghci> main
> users
1.) willkurt
2.) test
> tools
1.) hammer
 description: hits stuff
 last returned: 2024-03-14
 times borrowed: 2
2.) saw
 description: cuts stuff
 last returned: 2017-01-01
 times borrowed: 0
> a
Sorry command not found
> quit
bye!
ghci> :quit
Leaving GHCi.
```