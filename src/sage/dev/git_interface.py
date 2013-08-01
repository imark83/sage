r"""
AUTHORS:

- TODO: add authors from github's history and trac's history

#*****************************************************************************
#       Copyright (C) 2013 TODO
#
#  Distributed under the terms of the GNU General Public License (GPL)
#  as published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.env import SAGE_DOT_GIT, SAGE_REPO_AUTHENTICATED, SAGE_SRC

from git_error import GitError, DetachedHeadError

SILENT = object()
SUPER_SILENT = object()
READ_OUTPUT = object()
    r"""
    A wrapper around the ``git`` command line tool.

    Most methods of this class correspond to actual git commands. Some add
    functionality which is not directly available in git. However, all of the
    methods should be non-interactive. If interaction is required the method
    should live in :class:`saged.dev.sagedev.SageDev`.

    EXAMPLES::

        sage: from sage.dev.config import Config
        sage: from sage.dev.user_interface import UserInterface
        sage: from sage.dev.git_interface import GitInterface
        sage: config = Config()
        sage: GitInterface(config, UserInterface(config))
        GitInterface()

    """
        r"""
        Initialization.

        TESTS::

            sage: from sage.dev.config import Config
            sage: from sage.dev.user_interface import UserInterface
            sage: from sage.dev.git_interface import GitInterface
            sage: config = Config()
            sage: type(GitInterface(config, UserInterface(config)))
            <class 'sage.dev.git_interface.GitInterface'>

        """
        self._src = self._config.get('src', SAGE_SRC)
        self._repository = self._config.get('repository', SAGE_REPO_AUTHENTICATED)
        r"""
        Return a printable representation of this object.

            sage: from sage.dev.config import Config
            sage: from sage.dev.user_interface import UserInterface
            sage: from sage.dev.git_interface import GitInterface
            sage: config = Config()
            sage: repr(GitInterface(config, UserInterface(config)))

        r"""
        Get the current state of merge/rebase/am/etc operations.
        OUTPUT:
        A tuple of strings which consists of any of the following:
        ``'rebase'``, ``'am'``, ``'rebase-i'``, ``'rebase-m'``, ``'merge'``,
        ``'bisect'``, ``'cherry-seq'``, ``'cherry'``.

        EXAMPLES:

        Create a :class:`GitInterface` for doctesting::

            sage: import os
            sage: from sage.dev.git_interface import GitInterface, SILENT, SUPER_SILENT
            sage: from sage.dev.test.config import DoctestConfig
            sage: from sage.dev.test.user_interface import DoctestUserInterface
            sage: config = DoctestConfig()
            sage: git = GitInterface(config["git"], DoctestUserInterface(config["UI"]))

        Create two conflicting branches::

            sage: os.chdir(config['git']['src'])
            sage: with open("file","w") as f: f.write("version 0")
            sage: git.add("file")
            sage: git.commit(SUPER_SILENT, "-m","initial commit")
            sage: git.checkout(SUPER_SILENT, "-b","branch1")
            sage: with open("file","w") as f: f.write("version 1")
            sage: git.commit(SUPER_SILENT, "-am","second commit")
            sage: git.checkout(SUPER_SILENT, "master")
            sage: git.checkout(SUPER_SILENT, "-b","branch2")
            sage: with open("file","w") as f: f.write("version 2")
            sage: git.commit(SUPER_SILENT, "-am","conflicting commit")

        A ``merge`` state::

            sage: git.checkout(SUPER_SILENT, "branch1")
            sage: git.merge(SUPER_SILENT, 'branch2')
            Traceback (most recent call last):
            ...
            GitError: git returned with non-zero exit code (1)
            sage: git.merge(SUPER_SILENT,abort=True)

        A ``rebase`` state::

            sage: git.execute_supersilent('rebase', 'branch2')
            Traceback (most recent call last):
            ...
            GitError: git returned with non-zero exit code (1)
            sage: git.rebase(SUPER_SILENT, abort=True)

        A merge within an interactive rebase::

            sage: git.rebase(SUPER_SILENT, 'HEAD^', interactive=True, env={'GIT_SEQUENCE_EDITOR':'sed -i s+pick+edit+'})
            sage: git.merge(SUPER_SILENT, 'branch2')
            Traceback (most recent call last):
            ...
            GitError: git returned with non-zero exit code (1)
            sage: git.rebase(SUPER_SILENT, abort=True)

    def reset_to_clean_state(self):
        r"""
        Get out of a merge/am/rebase/etc state.
        EXAMPLES:
        Create a :class:`GitInterface` for doctesting::

            sage: import os
            sage: from sage.dev.git_interface import GitInterface, SILENT, SUPER_SILENT
            sage: from sage.dev.test.config import DoctestConfig
            sage: from sage.dev.test.user_interface import DoctestUserInterface
            sage: config = DoctestConfig()
            sage: git = GitInterface(config["git"], DoctestUserInterface(config["UI"]))

        Create two conflicting branches::

            sage: os.chdir(config['git']['src'])
            sage: with open("file","w") as f: f.write("version 0")
            sage: git.add("file")
            sage: git.commit(SUPER_SILENT, "-m","initial commit")
            sage: git.checkout(SUPER_SILENT, "-b","branch1")
            sage: with open("file","w") as f: f.write("version 1")
            sage: git.commit(SUPER_SILENT, "-am","second commit")
            sage: git.checkout(SUPER_SILENT, "master")
            sage: git.checkout(SUPER_SILENT, "-b","branch2")
            sage: with open("file","w") as f: f.write("version 2")
            sage: git.commit(SUPER_SILENT, "-am","conflicting commit")

        A merge within an interactive rebase::

            sage: git.checkout(SUPER_SILENT, "branch1")
            sage: git.rebase(SUPER_SILENT, 'HEAD^', interactive=True, env={'GIT_SEQUENCE_EDITOR':'sed -i s+pick+edit+'})
            ('rebase-i',)
            sage: git.merge(SUPER_SILENT, 'branch2')
            Traceback (most recent call last):
            ...
            GitError: git returned with non-zero exit code (1)

        Get out of this state::

            sage: git.reset_to_clean_state()

            return
        state = states[0]
        if state.startswith('rebase'):
            self.execute_silent('rebase', abort=True)
        elif state == 'am':
            self.execute_silent('am', abort=True)
        elif state == 'merge':
            self.execute_silent('merge', abort=True)
        elif state == 'bisect':
            raise NotImplementedError(state)
        elif state.startswith('cherry'):
            self.execute_silent('cherry-pick', abort=True)
        else:
            raise RuntimeError("'%s' is not a valid state"%state)
        return self.reset_to_clean_state()

    def reset_to_clean_working_directory(self, remove_untracked_files=False, remove_untracked_directories=False, remove_ignored=False):
        Reset any changes made to the working directory.
        INPUT:

        - ``remove_untracked_files`` -- a boolean (default: ``False``), whether
          to remove files which are not tracked by git

        - ``remove_untracked_directories`` -- a boolean (default: ``False``),
          whether to remove directories which are not tracked by git

        - ``remove_ignored`` -- a boolean (default: ``False``), whether to
          remove files directories which are ignored by git

        EXAMPLES:

        Create a :class:`GitInterface` for doctesting::
            sage: from sage.dev.git_interface import GitInterface, SILENT, SUPER_SILENT
            sage: from sage.dev.test.config import DoctestConfig
            sage: from sage.dev.test.user_interface import DoctestUserInterface
            sage: config = DoctestConfig()
            sage: git = GitInterface(config["git"], DoctestUserInterface(config["UI"]))

        Set up some files/directories::

            sage: os.chdir(config['git']['src'])
            sage: open('tracked','w').close()
            sage: git.add(SUPER_SILENT, 'tracked')
            sage: with open('.gitignore','w') as f: f.write('ignored\nignored_dir')
            sage: git.add(SUPER_SILENT, '.gitignore')
            sage: git.commit(SUPER_SILENT, '-m', 'initial commit')

            sage: os.mkdir('untracked_dir')
            sage: open('untracked_dir/untracked','w').close()
            sage: open('untracked','w').close()
            sage: open('ignored','w').close()
            sage: os.mkdir('ignored_dir')
            sage: open('ignored_dir/untracked','w').close()
            sage: with open('tracked','w') as f: f.write('version 0')
            sage: git.status()
            # On branch master
            # Changes not staged for commit:
            #   (use "git add <file>..." to update what will be committed)
            #   (use "git checkout -- <file>..." to discard changes in working directory)
            #
            #   modified:   tracked
            #
            # Untracked files:
            #   (use "git add <file>..." to include in what will be committed)
            #
            #   untracked
            #   untracked_dir/
            no changes added to commit (use "git add" and/or "git commit -a")

        Some invalid combinations of flags::

            sage: git.reset_to_clean_working_directory(remove_untracked_files = False, remove_untracked_directories = True)
            Traceback (most recent call last):
            ...
            ValueError: remove_untracked_directories only valid if remove_untracked_files is set
            sage: git.reset_to_clean_working_directory(remove_untracked_files = False, remove_ignored = True)
            Traceback (most recent call last):
            ...
            ValueError: remove_ignored only valid if remove_untracked_files is set

        Per default only the tracked modified files are reset to a clean
        state::

            sage: git.reset_to_clean_working_directory()
            sage: git.status()
            # On branch master
            # Untracked files:
            #   (use "git add <file>..." to include in what will be committed)
            #
            #   untracked
            #   untracked_dir/
            nothing added to commit but untracked files present (use "git add" to track)
        Untracked items can be removed by setting the parameters::

            sage: git.reset_to_clean_working_directory(remove_untracked_files=True)
            Removing untracked
            Not removing untracked_dir/
            sage: git.reset_to_clean_working_directory(remove_untracked_files=True, remove_untracked_directories=True)
            Removing untracked_dir/
            sage: git.reset_to_clean_working_directory(remove_untracked_files=True, remove_ignored=True)
            Removing ignored
            Not removing ignored_dir/
            sage: git.reset_to_clean_working_directory(remove_untracked_files=True, remove_untracked_directories=True, remove_ignored=True)
            Removing ignored_dir/

        """
        if remove_untracked_directories and not remove_untracked_files:
            raise ValueError("remove_untracked_directories only valid if remove_untracked_files is set")
        if remove_ignored and not remove_untracked_files:
            raise ValueError("remove_ignored only valid if remove_untracked_files is set")
        self.reset(SILENT, hard=True)
        if remove_untracked_files:
            switches = ['-f']
            if remove_untracked_directories: switches.append("-d")
            if remove_ignored: switches.append("-x")
            self.clean(*switches)
        Common implementation for :meth:`execute`, :meth:`execute_silent`,
        :meth:`execute_supersilent`, and :meth:`read_output`
          - ``stdout`` - if set to ``False`` will supress stdout
          - ``stderr`` - if set to ``False`` will supress stderr
            sage: import os
            sage: from sage.dev.git_interface import GitInterface
            sage: from sage.dev.test.config import DoctestConfig
            sage: from sage.dev.test.user_interface import DoctestUserInterface
            sage: config = DoctestConfig()
            sage: git = GitInterface(config["git"], DoctestUserInterface(config["UI"]))
            sage: os.chdir(config['git']['src'])

            sage: git._run_git('status', (), {})
            # On branch master
            # Initial commit
            #
            nothing to commit (create/copy files and use "git add" to track)

        TESTS:

        Check that we refuse to touch the live source code in doctests::

            sage: dev.git.status()
            Traceback (most recent call last):
            ...
            AssertionError: attempt to work with the live repository or directory in a doctest

        import sage.doctest
        import os
        assert not sage.doctest.DOCTEST_MODE or (self._dot_git != SAGE_DOT_GIT and self._repository != SAGE_REPO_AUTHENTICATED and os.path.abspath(os.getcwd()).startswith(self._src)), "attempt to work with the live repository or directory in a doctest"
        from sage.dev.user_interface import INFO
        self._UI.show("[git] %s"%(" ".join(s)), log_level=INFO)
        import subprocess
        r"""
        - ``cmd`` - git command run
        - ``args`` - extra arguments for git
        - ``kwds`` - extra keywords for git
            sage: import os
            sage: from sage.dev.git_interface import GitInterface
            sage: from sage.dev.test.config import DoctestConfig
            sage: from sage.dev.test.user_interface import DoctestUserInterface
            sage: config = DoctestConfig()
            sage: git = GitInterface(config["git"], DoctestUserInterface(config["UI"]))
            sage: os.chdir(config['git']['src'])

            sage: git.execute('status')
            # On branch master
            # Initial commit
            nothing to commit (create/copy files and use "git add" to track)
            sage: git.execute_silent('status',foo=True) # --foo is not a valid parameter
            Traceback (most recent call last):
            ...
            GitError: git returned with non-zero exit code (129)

        r"""
            sage: import os
            sage: from sage.dev.git_interface import GitInterface
            sage: from sage.dev.test.config import DoctestConfig
            sage: from sage.dev.test.user_interface import DoctestUserInterface
            sage: config = DoctestConfig()
            sage: git = GitInterface(config["git"], DoctestUserInterface(config["UI"]))
            sage: os.chdir(config['git']['src'])

            sage: git.execute_silent('status',foo=True) # --foo is not a valid parameter
            Traceback (most recent call last):
            ...
            GitError: git returned with non-zero exit code (129)

        r"""
            sage: import os
            sage: from sage.dev.git_interface import GitInterface
            sage: from sage.dev.test.config import DoctestConfig
            sage: from sage.dev.test.user_interface import DoctestUserInterface
            sage: config = DoctestConfig()
            sage: git = GitInterface(config["git"], DoctestUserInterface(config["UI"]))
            sage: os.chdir(config['git']['src'])

            sage: git.execute_supersilent('status',foo=True) # --foo is not a valid parameter
            Traceback (most recent call last):
            ...
            GitError: git returned with non-zero exit code (129)

            sage: import os
            sage: from sage.dev.git_interface import GitInterface
            sage: from sage.dev.test.config import DoctestConfig
            sage: from sage.dev.test.user_interface import DoctestUserInterface
            sage: config = DoctestConfig()
            sage: git = GitInterface(config["git"], DoctestUserInterface(config["UI"]))
            sage: os.chdir(config['git']['src'])

            sage: git.read_output('status')
            '# On branch master\n#\n# Initial commit\n#\nnothing to commit (create/copy files and use "git add" to track)\n'
            sage: git.read_output('status',foo=True) # --foo is not a valid parameter
            Traceback (most recent call last):
            ...
            GitError: git returned with non-zero exit code (129)

        r"""
        Return whether ``a`` is a child of ``b``.
        EXAMPLES:
        Create a :class:`GitInterface` for doctesting::

            sage: import os
            sage: from sage.dev.git_interface import GitInterface, SILENT, SUPER_SILENT
            sage: from sage.dev.test.config import DoctestConfig
            sage: from sage.dev.test.user_interface import DoctestUserInterface
            sage: config = DoctestConfig()
            sage: git = GitInterface(config["git"], DoctestUserInterface(config["UI"]))

        Create two conflicting branches::

            sage: os.chdir(config['git']['src'])
            sage: with open("file","w") as f: f.write("version 0")
            sage: git.add("file")
            sage: git.commit(SUPER_SILENT, "-m","initial commit")
            sage: git.checkout(SUPER_SILENT, "-b","branch1")
            sage: with open("file","w") as f: f.write("version 1")
            sage: git.commit(SUPER_SILENT, "-am","second commit")
            sage: git.checkout(SUPER_SILENT, "master")
            sage: git.checkout(SUPER_SILENT, "-b","branch2")
            sage: with open("file","w") as f: f.write("version 2")
            sage: git.commit(SUPER_SILENT, "-am","conflicting commit")

            sage: git.is_child_of('master', 'branch2')
            sage: git.is_child_of('branch2', 'master')
            sage: git.is_child_of('branch1', 'branch2')
            False
            sage: git.is_child_of('master', 'master')

        r"""
        Return whether ``a`` is an ancestor of ``b``.
        EXAMPLES:

        Create a :class:`GitInterface` for doctesting::
            sage: import os
            sage: from sage.dev.git_interface import GitInterface, SILENT, SUPER_SILENT
            sage: from sage.dev.test.config import DoctestConfig
            sage: from sage.dev.test.user_interface import DoctestUserInterface
            sage: config = DoctestConfig()
            sage: git = GitInterface(config["git"], DoctestUserInterface(config["UI"]))

        Create two conflicting branches::

            sage: os.chdir(config['git']['src'])
            sage: with open("file","w") as f: f.write("version 0")
            sage: git.add("file")
            sage: git.commit(SUPER_SILENT, "-m","initial commit")
            sage: git.checkout(SUPER_SILENT, "-b","branch1")
            sage: with open("file","w") as f: f.write("version 1")
            sage: git.commit(SUPER_SILENT, "-am","second commit")
            sage: git.checkout(SUPER_SILENT, "master")
            sage: git.checkout(SUPER_SILENT, "-b","branch2")
            sage: with open("file","w") as f: f.write("version 2")
            sage: git.commit(SUPER_SILENT, "-am","conflicting commit")

            sage: git.is_ancestor_of('master', 'branch2')
            sage: git.is_ancestor_of('branch2', 'master')
            False
            sage: git.is_ancestor_of('branch1', 'branch2')
            sage: git.is_ancestor_of('master', 'master')

        return not self.rev_list(READ_OUTPUT, '{}..{}'.format(b, a)).splitlines()
        Return whether there are uncommitted changes, i.e., whether there are
        modified files which are tracked by git.
        EXAMPLES:

        Create a :class:`GitInterface` for doctesting::
            sage: from sage.dev.git_interface import GitInterface, SILENT, SUPER_SILENT
            sage: from sage.dev.test.config import DoctestConfig
            sage: from sage.dev.test.user_interface import DoctestUserInterface
            sage: config = DoctestConfig()
            sage: git = GitInterface(config["git"], DoctestUserInterface(config["UI"]))

        An untracked file does not count towards uncommited changes::

            sage: os.chdir(config['git']['src'])
            sage: open('untracked','w').close()
        Once added to the index it does::
            sage: git.add('untracked')
            sage: git.commit(SUPER_SILENT, '-m', 'tracking untracked')
            sage: with open('untracked','w') as f: f.write('version 0')
            sage: git.has_uncommitted_changes()
            True
        return bool([line for line in self.status(READ_OUTPUT, porcelain=True).splitlines() if not line.startswith('?')])
    def untracked_files(self):
        r"""
        Return a list of file names for files that are not tracked by git and
        not ignored.
        EXAMPLES:
        Create a :class:`GitInterface` for doctesting::
            sage: import os
            sage: from sage.dev.git_interface import GitInterface, SILENT, SUPER_SILENT
            sage: from sage.dev.test.config import DoctestConfig
            sage: from sage.dev.test.user_interface import DoctestUserInterface
            sage: config = DoctestConfig()
            sage: git = GitInterface(config["git"], DoctestUserInterface(config["UI"]))
        An untracked file::
            sage: os.chdir(config['git']['src'])
            sage: git.untracked_files()
            []
            sage: open('untracked','w').close()
            sage: git.untracked_files()
            ['untracked']
         Directories are not displayed here::
            sage: os.mkdir('untracked_dir')
            sage: git.untracked_files()
            ['untracked']
            sage: open('untracked_dir/untracked','w').close()
            sage: git.untracked_files()
            ['untracked', 'untracked_dir/untracked']
        return self.read_output('ls-files', other=True, exclude_standard=True).splitlines()
    def local_branches(self):
        r"""
        Return a list of local branches sorted by last commit time.
        Create a :class:`GitInterface` for doctesting::

            sage: import os
            sage: from sage.dev.git_interface import GitInterface, SILENT, SUPER_SILENT
            sage: from sage.dev.test.config import DoctestConfig
            sage: from sage.dev.test.user_interface import DoctestUserInterface
            sage: config = DoctestConfig()
            sage: git = GitInterface(config["git"], DoctestUserInterface(config["UI"]))

        Create some branches::

            sage: os.chdir(config['git']['src'])
            sage: git.commit(SILENT, '-m','initial commit','--allow-empty')
            sage: git.branch('branch1')
            sage: git.branch('branch2')

        Use this repository as a remote repository::

            sage: config2 = DoctestConfig()
            sage: git2 = GitInterface(config2["git"], DoctestUserInterface(config["UI"]))
            sage: os.chdir(config2['git']['src'])
            sage: git2.commit(SILENT, '-m','initial commit','--allow-empty')
            sage: git2.remote('add', 'git', config['git']['src'])
            sage: git2.fetch(SUPER_SILENT, 'git')
            sage: git2.checkout(SUPER_SILENT, "branch1")
            sage: git2.branch("-a")
            * branch1
              master
              remotes/git/branch1
              remotes/git/branch2
              remotes/git/master

            sage: git2.local_branches()
            ['branch1', 'master']
            sage: os.chdir(config['git']['src'])
            sage: git.local_branches()
            ['branch1', 'branch2', 'master']
        result = self.for_each_ref(READ_OUTPUT, 'refs/heads/',
                    sort='-committerdate', format="%(refname)").splitlines()
        return [head[11:] for head in result]
    def current_branch(self):
        r"""
        Return the current branch
        EXAMPLES:
        Create a :class:`GitInterface` for doctesting::
            sage: import os
            sage: from sage.dev.git_interface import GitInterface, SILENT, SUPER_SILENT
            sage: from sage.dev.test.config import DoctestConfig
            sage: from sage.dev.test.user_interface import DoctestUserInterface
            sage: config = DoctestConfig()
            sage: git = GitInterface(config["git"], DoctestUserInterface(config["UI"]))
        Create some branches::
            sage: os.chdir(config['git']['src'])
            sage: git.commit(SILENT, '-m','initial commit','--allow-empty')
            sage: git.commit(SILENT, '-m','second commit','--allow-empty')
            sage: git.branch('branch1')
            sage: git.branch('branch2')
            sage: git.current_branch()
            'master'
            sage: git.checkout(SUPER_SILENT, 'branch1')
            sage: git.current_branch()
            'branch1'
        If ``HEAD`` is detached::
            sage: git.checkout(SUPER_SILENT, 'master~')
            sage: git.current_branch()
            Traceback (most recent call last):
            ...
            DetachedHeadError: unexpectedly, git is in a detached HEAD state
            return self.symbolic_ref(READ_OUTPUT, 'HEAD', short=True, quiet=True).strip()
        except GitError as e:
            if e.exit_code == 1:
               raise DetachedHeadError()
            raise
    def commit_for_branch(self, branch):
        r"""
        Return the commit id of the local ``branch``, or ``None`` if the branch
        does not exist
        EXAMPLES:
        Create a :class:`GitInterface` for doctesting::
            sage: import os
            sage: from sage.dev.git_interface import GitInterface, SILENT, SUPER_SILENT
            sage: from sage.dev.test.config import DoctestConfig
            sage: from sage.dev.test.user_interface import DoctestUserInterface
            sage: config = DoctestConfig()
            sage: git = GitInterface(config["git"], DoctestUserInterface(config["UI"]))
        Create some branches::
            sage: os.chdir(config['git']['src'])
            sage: git.commit(SILENT, '-m','initial commit','--allow-empty')
            sage: git.branch('branch1')
            sage: git.branch('branch2')
        Check existence of branches::
            sage: git.commit_for_branch('branch1') # random output
            '087e1fdd0fe6f4c596f5db22bc54567b032f5d2b'
            sage: git.commit_for_branch('branch2') is not None
            sage: git.commit_for_branch('branch3') is not None
            False
        return self.commit_for_ref("refs/heads/%s"%branch)
    def commit_for_ref(self, ref):
        Return the commit id of the ``ref``, or ``None`` if the ``ref`` does
        not exist.
        EXAMPLES:
        Create a :class:`GitInterface` for doctesting::
            sage: import os
            sage: from sage.dev.git_interface import GitInterface, SILENT, SUPER_SILENT
            sage: from sage.dev.test.config import DoctestConfig
            sage: from sage.dev.test.user_interface import DoctestUserInterface
            sage: config = DoctestConfig()
            sage: git = GitInterface(config["git"], DoctestUserInterface(config["UI"]))
        Create some branches::
            sage: os.chdir(config['git']['src'])
            sage: git.commit(SILENT, '-m','initial commit','--allow-empty')
            sage: git.branch('branch1')
            sage: git.branch('branch2')
        Check existence of branches::
            sage: git.commit_for_ref('refs/heads/branch1') # random output
            '087e1fdd0fe6f4c596f5db22bc54567b032f5d2b'
            sage: git.commit_for_ref('refs/heads/branch2') is not None
            sage: git.commit_for_ref('refs/heads/branch3') is not None
        try:
            return self.show_ref(READ_OUTPUT, ref, hash=True, verify=True).strip()
        except GitError:
            return None
    def rename_branch(self, oldname, newname):
        r"""
        Rename ``oldname`` to ``newname``.
        EXAMPLES:
        Create a :class:`GitInterface` for doctesting::
            sage: from sage.dev.git_interface import GitInterface, SILENT, SUPER_SILENT
            sage: from sage.dev.test.config import DoctestConfig
            sage: from sage.dev.test.user_interface import DoctestUserInterface
            sage: config = DoctestConfig()
            sage: git = GitInterface(config["git"], DoctestUserInterface(config["UI"]))
        Create some branches::
            sage: os.chdir(config['git']['src'])
            sage: git.commit(SILENT, '-m','initial commit','--allow-empty')
            sage: git.branch('branch1')
            sage: git.branch('branch2')
        Rename some branches::
            sage: git.rename_branch('branch1', 'branch3')
            sage: git.rename_branch('branch2', 'branch3')
            GitError: git returned with non-zero exit code (128)
        """
        self.branch(oldname, newname, move=True)
for git_cmd_ in (
        "for_each_ref",
        "init",
        "remote",
        "rev_list",
        "show_ref",
        "symbolic_ref",
        "tag"
    def create_wrapper(git_cmd__):
        r"""
        Create a wrapper for `git_cmd__`.

        EXAMPLES::

            sage: import os
            sage: from sage.dev.git_interface import GitInterface, SILENT, SUPER_SILENT
            sage: from sage.dev.test.config import DoctestConfig
            sage: from sage.dev.test.user_interface import DoctestUserInterface
            sage: config = DoctestConfig()
            sage: git = GitInterface(config["git"], DoctestUserInterface(config["UI"]))
            sage: os.chdir(config['git']['src'])
            sage: git.status()
            # On branch master
            #
            # Initial commit
            #
            nothing to commit (create/copy files and use "git add" to track)

        """
        git_cmd = git_cmd__.replace("_","-")
        def meth(self, *args, **kwds):
            args = list(args)
            if len([arg for arg in args if arg in (SILENT, SUPER_SILENT, READ_OUTPUT)]) > 1:
                raise ValueError("at most one of SILENT, SUPER_SILENT, READ_OUTPUT allowed")
            if SILENT in args:
                args.remove(SILENT)
                return self.execute_silent(git_cmd, *args, **kwds)
            elif SUPER_SILENT in args:
                args.remove(SUPER_SILENT)
                return self.execute_supersilent(git_cmd, *args, **kwds)
            elif READ_OUTPUT in args:
                args.remove(READ_OUTPUT)
                return self.read_output(git_cmd, *args, **kwds)
            else:
                return self.execute(git_cmd, *args, **kwds)
        meth.__doc__ = r"""
        Call `git {0}`.

        If `args` contains ``SILENT``, then output to stdout is supressed.

        If `args` contains ``SUPER_SILENT``, then output to stdout and stderr
        is supressed.

        OUTPUT:

        Returns ``None`` unless `args` contains ``READ_OUTPUT``; in that case,
        the commands output to stdout is returned.

        See :meth:`execute` for more information.

        EXAMPLES:

            sage: dev.git.{1}() # not tested
        """.format(git_cmd, git_cmd__)
        return meth
    setattr(GitInterface, git_cmd_, create_wrapper(git_cmd_))