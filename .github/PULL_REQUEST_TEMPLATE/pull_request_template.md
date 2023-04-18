**Description**

<!-- 
Please include a summary of the changes and which issue is fixed or which feature it added.
Please also include relevant motivation and context. List any dependencies that are required for this change.
-->

<!--
If Connected to an issue, include:
Closes # (issue)
-->

**Type of change**

<!-- Choose those that fit the type of your change

- Bug fix (change which fixes an issue)
- New feature (change which adds functionality)
- Update to functionality
- Other: <add other type here> 
-->

**Testing**

<!-- Please shortly describe how you tested your code and mark all you have done after -->

- [ ] I added basic working examples (possibly in doc-comment)
<!-- exclude the following if it does not apply -->
- [ ] I added tests for large (pointer representation) values
- [ ] I triggered all possible errors in my test in every possible way
- [ ] I included assertions in which I compare expected values with computed values
<!-- Please add other tests if any other have been performed -->

**Checklist:**

<!-- This is a short summary of the things the programmer should always consider before merging-->

- [ ] I have performed a self-review of my own code
  - [ ] Design choice fits code base + good time to do the PR
  - [ ] The added lines provide good readability (naming, comments, documentation, spelling)
  - [ ] The code fits our style guide
  - [ ] I included tests for all reasonable edge cases
  - [ ] My code works as intended and no side effects occur (e.g. memory leaks)
  - [ ] The chosen implementation is not more complex than it has to be
  - [ ] My code is not missing any crucial feature (or if it is listed as another task)
  - [ ] My code uses encapsulation and modularization
  - [ ] `cargo doc` does not generate any errors
  - [ ] I have credited related sources if needed